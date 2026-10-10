import OAI.Analysis.LipschitzHilbert.Estimates.ComparableDerivativeSum
import OAI.Analysis.LipschitzHilbert.Estimates.SmoothCarlesonSynthesis

namespace OAI

/-! The full comparable-frequency contribution, with its two product
terms estimated by actual smooth Carleson synthesis. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation
open DyadicLineGrid

theorem schwartzDerivative_lipschitz_bound (b : SchwartzMap ℝ ℂ) (L : ℝ)
    (hLip : ∀ x y, ‖b x-b y‖≤L*|x-y|) : 0≤L ∧ ∀ x, ‖schwartzDerivative 1 b x‖≤L := by
  have hL : 0≤L := by
    have hh := hLip 1 0
    norm_num at hh
    exact (norm_nonneg _).trans hh
  refine ⟨hL,fun x => ?_⟩
  change ‖deriv b x‖≤L
  exact norm_deriv_le_of_lip' hL (Filter.Eventually.of_forall fun y => by
    simpa only [Real.norm_eq_abs] using hLip y x)

theorem lineSchwartz_three_energy (f g h : SchwartzMap ℝ ℂ) :
    (∫ x, ‖(f-g+h) x‖^2)≤3*((∫ x, ‖f x‖^2)+(∫ x, ‖g x‖^2)+(∫ x, ‖h x‖^2)) := by
  have hi (p : SchwartzMap ℝ ℂ) : Integrable (fun x => ‖p x‖^2) :=
    (p.memLp 2 volume).integrable_norm_pow (by decide : 2≠0)
  calc
    _ ≤ ∫ x, 3*(‖f x‖^2+‖g x‖^2+‖h x‖^2) := by
      apply integral_mono (hi _) (((hi f).add (hi g)).add (hi h) |>.const_mul 3)
      intro x
      simp only [add_apply,sub_apply]
      change ‖f x-g x+h x‖^2≤3*(‖f x‖^2+‖g x‖^2+‖h x‖^2)
      have ht : ‖f x-g x+h x‖≤‖f x‖+‖g x‖+‖h x‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) (le_refl _))
      have hs := pow_le_pow_left₀ (norm_nonneg _) ht 2
      nlinarith [sq_nonneg (‖f x‖-‖g x‖),sq_nonneg (‖f x‖-‖h x‖),sq_nonneg (‖g x‖-‖h x‖)]
    _ = _ := by
      rw [integral_const_mul,
        integral_add (f:=fun x => ‖f x‖^2+‖g x‖^2) (g:=fun x => ‖h x‖^2) ((hi f).add (hi g)) (hi h),
        integral_add (hi f) (hi g)]

theorem lineSchwartzProjection_sum {ι : Type*} (I : Finset ι)
    (q : SchwartzMap ℝ ℂ) (W : ℝ) (hW : W≠0) (f : ι → SchwartzMap ℝ ℂ) :
    lineSchwartzProjection q W hW (∑ i∈I, f i)=∑ i∈I, lineSchwartzProjection q W hW (f i) :=
  map_sum (lineSchwartzProjectionLM q W hW) f I

def comparableCommutatorConstant : ℝ :=
  3*(48*(16384*((∫ t, |t| *‖(𝓕⁻ dyadicDifference : SchwartzMap ℝ ℂ) t‖)*
    (52*Real.pi/3)))^2+2*smoothCarlesonDualConstant)

theorem comparableCommutatorSum_energy (I : Finset ℤ) (m b : SchwartzMap ℝ ℂ)
    (H : ℤ → SchwartzMap ℝ ℂ) (A L : ℝ)
    (hm : ∀ eta, ‖m eta‖≤A) (hLip : ∀ x y, ‖b x-b y‖≤L*|x-y|)
    (hH : ∀ k∈I, ∀ eta, (𝓕 (H k) : SchwartzMap ℝ ℂ) eta≠0 → |eta|≤64/scale k) :
    (∫ x, ‖(∑ k∈I, lineSchwartzCommutator m
      (lineSchwartzProjection dyadicDifference (scale k) (scale_pos k).ne' b)
      (schwartzDerivative 1 (H k))) x‖^2)≤
        comparableCommutatorConstant*A^2*L^2*(∑ k∈I, ∫ x, ‖H k x‖^2) := by
  let T := lineSchwartzProjection m 1 (by norm_num)
  let d := schwartzDerivative 1 b
  let U := ∑ k∈I, comparableDerivativePiece m b H k
  let V := dyadicParaproduct I d (fun k => T (H k))
  let Z := T (dyadicParaproduct I d H)
  let E := ∑ k∈I, ∫ x, ‖H k x‖^2
  obtain ⟨hL,hdb⟩ := schwartzDerivative_lipschitz_bound b L hLip
  have hTH (k : ℤ) (hk : k∈I) (eta : ℝ)
      (heta : (𝓕 (T (H k)) : SchwartzMap ℝ ℂ) eta≠0) : |eta|≤64/scale k :=
    hH k hk eta (lineSchwartzProjection_frequency_of_nonzero m (H k) 1 (by norm_num) eta heta)
  have hTE : (∑ k∈I, ∫ x, ‖T (H k) x‖^2)≤A^2*E := by
    calc
      _ ≤ ∑ k∈I, A^2*(∫ x, ‖H k x‖^2) :=
        Finset.sum_le_sum (fun k _ => lineSchwartzProjection_energy m 1 (by norm_num) A hm (H k))
      _ = _ := (Finset.mul_sum I _ _).symm
  have hV : (∫ x, ‖V x‖^2)≤smoothCarlesonDualConstant*L^2*(A^2*E) :=
    (smooth_carleson_synthesis I d L hL hdb (fun k => T (H k)) hTH).trans
      (mul_le_mul_of_nonneg_left hTE (mul_nonneg smoothCarlesonDualConstant_nonneg (sq_nonneg L)))
  have hZ : (∫ x, ‖Z x‖^2)≤A^2*(smoothCarlesonDualConstant*L^2*E) :=
    (lineSchwartzProjection_energy m 1 (by norm_num) A hm _).trans
      (mul_le_mul_of_nonneg_left (smooth_carleson_synthesis I d L hL hdb H hH) (sq_nonneg A))
  have hU := comparableDerivativeSum_energy I m b H A L hm hLip hH
  have he : (∑ k∈I, lineSchwartzCommutator m
      (lineSchwartzProjection dyadicDifference (scale k) (scale_pos k).ne' b)
      (schwartzDerivative 1 (H k)))=U-V+Z := by
    simp_rw [lineSchwartzCommutator_derivative_identity,lineSchwartzProjection_derivative]
    simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib]
    rw [←lineSchwartzProjection_sum]
    rfl
  rw [he]
  calc
    _ ≤ 3*((∫ x, ‖U x‖^2)+(∫ x, ‖V x‖^2)+(∫ x, ‖Z x‖^2)) := lineSchwartz_three_energy U V Z
    _ ≤ 3*(48*(16384*(A*L*(∫ t, |t| *‖(𝓕⁻ dyadicDifference : SchwartzMap ℝ ℂ) t‖)*
        (52*Real.pi/3)))^2*E+smoothCarlesonDualConstant*L^2*(A^2*E)+
        A^2*(smoothCarlesonDualConstant*L^2*E)) := by
      gcongr
    _ = _ := by dsimp [comparableCommutatorConstant,E]; ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
