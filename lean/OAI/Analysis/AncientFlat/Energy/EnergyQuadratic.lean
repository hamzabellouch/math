import OAI.Analysis.AncientFlat.Energy.EnergyLaplacian

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Laplacian
namespace ParametrixUniqueness
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
def mass (f : V → ℂ) : ℝ := ∫ x, weight x*‖f x‖^2
def cross (f g : V → ℂ) : ℝ := ∫ x, weight x*(‖f x‖*‖g x‖)
def pair (f g : V → ℂ) : ℝ := ∫ x, weight x*inner ℝ (f x) (g x)
lemma integrable_mass {f : V → ℂ} (hc : Continuous f) (hb : Bounded f) :
    Integrable (fun x => weight x*‖f x‖^2) := by
  simpa only [pow_two] using (decays_weight_mul (hb.norm.mul hb.norm)).integrable
    ((contDiff_weight 0).continuous.mul (hc.norm.mul hc.norm))
lemma integrable_cross {f g : V → ℂ} (hc : Continuous f) (hd : Continuous g)
    (hb : Bounded f) (he : Bounded g) : Integrable (fun x => weight x*(‖f x‖*‖g x‖)) :=
  (decays_weight_mul (hb.norm.mul he.norm)).integrable
    ((contDiff_weight 0).continuous.mul (hc.norm.mul hd.norm))
lemma integrable_pair {f g : V → ℂ} (hc : Continuous f) (hd : Continuous g)
    (hb : Bounded f) (he : Bounded g) : Integrable (fun x => weight x*inner ℝ (f x) (g x)) :=
  (decays_weight_mul (hb.inner he)).integrable
    ((contDiff_weight 0).continuous.mul (hc.inner hd))
lemma mass_nonneg (f : V → ℂ) : 0 ≤ mass f :=
  integral_nonneg (fun x => mul_nonneg (weight_pos x).le (sq_nonneg _))
lemma cross_nonneg (f g : V → ℂ) : 0 ≤ cross f g :=
  integral_nonneg (fun x => mul_nonneg (weight_pos x).le (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
lemma weighted_young {f g : V → ℂ} (hc : Continuous f) (hd : Continuous g)
    (hb : Bounded f) (he : Bounded g) (ε : ℝ) (hε : 0<ε) :
    2*cross f g ≤ ε*mass f + ε⁻¹*mass g := by
  have hf := integrable_mass hc hb
  have hg := integrable_mass hd he
  have hfg := integrable_cross hc hd hb he
  calc
    _ = ∫ x, weight x*(2*‖f x‖*‖g x‖) := by rw [cross,←integral_const_mul]; congr 1; funext x; ring
    _ ≤ ∫ x, weight x*(ε*‖f x‖^2+ε⁻¹*‖g x‖^2) := by
      apply integral_mono
      · convert hfg.const_mul 2 using 1; funext x; ring
      · exact ((hf.const_mul ε).add (hg.const_mul ε⁻¹)).congr
          (Eventually.of_forall (fun x => by simp only [Pi.add_apply]; ring))
      · intro x
        apply mul_le_mul_of_nonneg_left _ (weight_pos x).le
        have hh := sq_nonneg (ε*‖f x‖-‖g x‖)
        have hn : ε⁻¹*ε=1 := inv_mul_cancel₀ (ne_of_gt hε)
        nlinarith
    _ = _ := by
      rw [show (fun x => weight x*(ε*‖f x‖^2+ε⁻¹*‖g x‖^2)) =
        (fun x => ε*(weight x*‖f x‖^2)+ε⁻¹*(weight x*‖g x‖^2)) by funext x; ring,
        integral_add (hf.const_mul ε) (hg.const_mul ε⁻¹),integral_const_mul,integral_const_mul]
      rfl
lemma abs_coeff_pair_le {f g : V → ℂ} (hc : Continuous f) (hd : Continuous g)
    (hb : Bounded f) (he : Bounded g) (c : V → ℝ) (hc' : Continuous c)
    (M : ℝ) (hM : 0≤M) (hcm : ∀ x, |c x|≤M*weight x) :
    |∫ x, c x*inner ℝ (f x) (g x)| ≤ M*cross f g := by
  have hi : Integrable (fun x => c x*inner ℝ (f x) (g x)) :=
    (Decays.smul (g := fun x => inner ℝ (f x) (g x)) ⟨M,hM,fun x => hcm x⟩
      (hb.inner he)).integrable (hc'.mul (hc.inner hd))
  calc
    _ ≤ ∫ x, ‖c x*inner ℝ (f x) (g x)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, M*(weight x*(‖f x‖*‖g x‖)) := by
      apply integral_mono hi.norm ((integrable_cross hc hd hb he).const_mul M)
      intro x
      change |c x*inner ℝ (f x) (g x)| ≤ M*(weight x*(‖f x‖*‖g x‖))
      rw [abs_mul]
      calc
        _ ≤ (M*weight x)*(‖f x‖*‖g x‖) := mul_le_mul (hcm x)
          (norm_inner_le_norm (𝕜 := ℝ) (f x) (g x)) (norm_nonneg _) (mul_nonneg hM (weight_pos x).le)
        _ = _ := by ring
    _ = _ := integral_const_mul _ _
lemma abs_pair_le {f g : V → ℂ} (hc : Continuous f) (hd : Continuous g)
    (hb : Bounded f) (he : Bounded g) : |pair f g|≤cross f g := by
  simpa only [one_mul,pair] using abs_coeff_pair_le hc hd hb he weight (contDiff_weight 0).continuous
    1 (by norm_num) (fun x => by rw [abs_of_pos (weight_pos x),one_mul])
end ParametrixUniqueness

end

end OAI
