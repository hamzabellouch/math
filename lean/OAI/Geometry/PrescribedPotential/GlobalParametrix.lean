import Mathlib
import OAI.Geometry.PrescribedPotential.GlobalTransport
import OAI.Geometry.PrescribedPotential.IntegerBounds
import OAI.Geometry.PrescribedPotential.PatchCutoffs

namespace OAI

/-! Global Parametrix. -/

section

 

noncomputable section
open Set Filter Topology _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped SchwartzMap ContDiff Classical ComplexOrder MatrixOrder

namespace Anticanonical.SourceSmooth.ParametrixPatch
open EllipticKernel SobolevChart FrozenPoisson ParameterRegularity
variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}
  {g : KaehlerMetric A}

abbrev matrix (p : ParametrixPatch g) := g.matrix p.index (coordinateEquiv d p.center)
lemma positive (p : ParametrixPatch g) : p.matrix.PosDef :=
  g.positive p.index _ (by simpa using p.mem_target)

 

def localInverse (p : ParametrixPatch g) (m : ℝ) (hm : 1 ≤ m) :
    𝓢(EC d, ℂ) →ₗ[ℝ] 𝓢(EC d, ℂ) :=
  (schwartzLocal p.matrix p.positive m hm (stdOrthonormalBasis ℝ (EC d))
    p.coefficient p.small).restrictScalars ℝ

lemma localInverse_bound (p : ParametrixPatch g) (m : ℝ) (hm : 1 ≤ m) (k : ℕ) :
    CoreBound (k : ℝ) ((k : ℝ) + 2) (p.localInverse m hm) :=
  schwartzLocal_integer_bound p.matrix p.positive m hm (stdOrthonormalBasis ℝ (EC d))
    p.coefficient p.small k
end Anticanonical.SourceSmooth.ParametrixPatch

namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]

theorem globalize_integer_bound (D : Localizers A ι)
    (i : Fin A.count) (κ : ChartCutoff (A.euclideanChart i).target) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : 𝓢(EC d, ℂ),
      ‖D.embed (k : ℝ) (globalize i κ f)‖ ≤ C * ‖schwartzCoord (k : ℝ) f‖ := by
  have hB (j : ι) : CoreBound (k : ℝ) (k : ℝ)
      (fun f => localize A (D.index j) (D.weight j) (D.support_sub j) (globalize i κ f)) := by
    simp_rw [localize_globalize]
    exact chartTransport_integer_bound _ (A.euclidean_transition_smooth (D.index j) i)
      (A.euclidean_transition_smooth i (D.index j)) _ k
  choose C hC h using hB
  refine ⟨∑ j, C j, Finset.sum_nonneg (fun j _ => hC j), fun f => ?_⟩
  change ‖D.coordinates (k : ℝ) (globalize i κ f)‖ ≤ _
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (Finset.sum_nonneg (fun j _ => hC j)) (norm_nonneg _))).mpr
  intro j
  exact (h j f).trans (mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ j)) (norm_nonneg _))

namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)

def forcing (p : ι) : Smooth A →ₗ[ℝ] 𝓢(EC d, ℂ) :=
  localizeLinear A (D.localizers.index p) (D.localizers.weight p) (D.localizers.support_sub p)

lemma forcing_bound (p : ι) (s : ℝ) (f : Smooth A) :
    ‖schwartzCoord s (D.forcing p f)‖ ≤ ‖D.localizers.embed s f‖ :=
  norm_le_pi_norm (D.localizers.coordinates s f) p

 
def parametrix (m : ℝ) (hm : 1 ≤ m) : Smooth A →ₗ[ℝ] Smooth A :=
  ∑ p, (globalize (D.patch p).index (D.cutoff p)).comp
    (((D.patch p).localInverse m hm).comp (D.forcing p))

lemma parametrix_apply (m : ℝ) (hm : 1 ≤ m) (f : Smooth A) :
    D.parametrix m hm f = ∑ p, globalize (D.patch p).index (D.cutoff p)
      ((D.patch p).localInverse m hm (D.forcing p f)) := by
  simp only [parametrix, LinearMap.sum_apply, LinearMap.comp_apply]

lemma parametrix_piece_bound (m : ℝ) (hm : 1 ≤ m) (k : ℕ) (p : ι) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Smooth A,
      ‖D.localizers.embed ((k : ℝ) + 2) (globalize (D.patch p).index (D.cutoff p)
        ((D.patch p).localInverse m hm (D.forcing p f)))‖ ≤
        C * ‖D.localizers.embed (k : ℝ) f‖ := by
  obtain ⟨B, hB, hb⟩ := globalize_integer_bound D.localizers (D.patch p).index (D.cutoff p) (k + 2)
  obtain ⟨C, hC, hc⟩ := (D.patch p).localInverse_bound m hm k
  refine ⟨B * C, mul_nonneg hB hC, fun f => ?_⟩
  have hh := hb ((D.patch p).localInverse m hm (D.forcing p f))
  rw [Nat.cast_add, Nat.cast_ofNat] at hh
  apply hh.trans
  have hr := (hc (D.forcing p f)).trans
    (mul_le_mul_of_nonneg_left (D.forcing_bound p (k : ℝ) f) hC)
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hr hB

 
lemma parametrix_bound (m : ℝ) (hm : 1 ≤ m) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Smooth A,
      ‖D.localizers.embed ((k : ℝ) + 2) (D.parametrix m hm f)‖ ≤
        C * ‖D.localizers.embed (k : ℝ) f‖ := by
  choose C hC hc using D.parametrix_piece_bound m hm k
  refine ⟨∑ p, C p, Finset.sum_nonneg (fun p _ => hC p), fun f => ?_⟩
  rw [parametrix_apply, map_sum, Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  exact Finset.sum_le_sum (fun p _ => hc p f)

 

lemma forcing_reconstruction (f : Smooth A) :
    (∑ p, globalize (D.patch p).index (D.cutoff p) (D.forcing p f)) = f := by
  apply Smooth.ext
  intro x
  have he (p : ι) : globalize (D.patch p).index (D.cutoff p) (D.forcing p f) x =
      D.localizers.weight p x * f x := by
    by_cases hx : x ∈ tsupport (D.localizers.weight p : X → ℂ)
    · have hp := (D.support_patch p hx).1
      rw [globalize_apply, ite_eq_left hp, D.cutoff_one p x hx, one_mul]
      change localizeFun A (D.localizers.index p) (D.localizers.weight p) f
        (A.euclideanChart (D.patch p).index x) = _
      rw [D.index_eq, localizeFun_apply A _ _ ((A.euclideanChart (D.patch p).index).mapsTo hp),
        (A.euclideanChart (D.patch p).index).left_inv hp]
    · have hz := image_eq_zero_of_notMem_tsupport hx
      rw [hz, zero_mul, globalize_apply]
      split_ifs with hp
      · change D.cutoff p _ * (localizeFun A (D.localizers.index p) (D.localizers.weight p) f _) = 0
        rw [D.index_eq, localizeFun_apply A _ _ ((A.euclideanChart (D.patch p).index).mapsTo hp),
          (A.euclideanChart (D.patch p).index).left_inv hp, hz, zero_mul, mul_zero]
      · rfl
  change (∑ p, (globalize (D.patch p).index (D.cutoff p) (D.forcing p f) : Smooth A)) x = _
  have hev (S : Finset ι) (F : ι → Smooth A) : (∑ p ∈ S, F p) x = ∑ p ∈ S, F p x := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert p S hp ih => simp only [Finset.sum_insert hp, Smooth.add_apply, ih]
  rw [hev]
  simp_rw [he]
  rw [← Finset.sum_mul, D.localizers.sum_one, one_mul]

end GluingData
end GlobalElliptic

end
end

end OAI
