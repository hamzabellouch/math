import OAI.Probability.ContinuumTransition.GrandLinearity

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature

structure GrandFinite (F : ConfigFamily) (D : Set Space) : Prop where
  integrable : ∀ (ι : Type) [Fintype ι], IntegrableOn (F ι) {x | ∀ i, x i ∈ D}
  summable : Summable (familyTerm F D)

theorem GrandFinite.of_bound (F : ConfigFamily) {D : Set Space} (hD : volume D ≠ ⊤)
    {d : ℝ} (hm : ∀ (ι : Type) [Fintype ι], Measurable (F ι))
    (h0 : ∀ (ι : Type) [Fintype ι] (x : ι → Space), 0 ≤ F ι x)
    (hb : ∀ (ι : Type) [Fintype ι] (x : ι → Space), F ι x ≤ Real.exp (d*Fintype.card ι)) :
    GrandFinite F D where
  integrable := fun ι _ => integrableOn_family_of_bound F hD (hm ι) (h0 ι) (hb ι)
  summable := summable_familyTerm_of_bound F hD hm h0 hb

theorem GrandFinite.const_mul {F : ConfigFamily} {D : Set Space}
    (hF : GrandFinite F D) (c : ℝ) : GrandFinite (fun ι _ x => c*F ι x) D where
  integrable := fun ι _ => (hF.integrable ι).const_mul c
  summable := by
    change Summable (fun n => familyTerm (fun ι _ x => c*F ι x) D n)
    simp_rw [familyTerm_const_mul]
    exact hF.summable.mul_left c

theorem GrandFinite.add {F G : ConfigFamily} {D : Set Space}
    (hF : GrandFinite F D) (hG : GrandFinite G D) :
    GrandFinite (fun ι _ x => F ι x+G ι x) D where
  integrable := fun ι _ => (hF.integrable ι).add (hG.integrable ι)
  summable := by
    change Summable (fun n => familyTerm (fun ι _ x => F ι x+G ι x) D n)
    simp_rw [familyTerm_add F G D _ (hF.integrable _) (hG.integrable _)]
    exact hF.summable.add hG.summable

theorem GrandFinite.sum {κ : Type} [Fintype κ] (F : κ → ConfigFamily) {D : Set Space}
    (hF : ∀ j, GrandFinite (F j) D) : GrandFinite (fun ι _ x => ∑ j, F j ι x) D where
  integrable := fun ι _ => integrable_finsetSum _ (fun j _ => (hF j).integrable ι)
  summable := by
    change Summable (fun n => familyTerm (fun ι _ x => ∑ j, F j ι x) D n)
    simp_rw [familyTerm_sum F D _ (fun j => (hF j).integrable _)]
    exact summable_sum (fun j _ => (hF j).summable)

theorem GrandFinite.mono_set {F : ConfigFamily} {A D : Set Space}
    (hF : GrandFinite F D) (hAD : A ⊆ D)
    (h0 : ∀ (ι : Type) [Fintype ι] (x : ι → Space), 0 ≤ F ι x) : GrandFinite F A where
  integrable := fun ι _ => (hF.integrable ι).mono_set (fun _ hx i => hAD (hx i))
  summable := by
    apply Summable.of_nonneg_of_le (familyTerm_nonneg F A h0) _ hF.summable
    intro n
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    apply setIntegral_mono_set (hF.integrable (Fin n)) (Filter.Eventually.of_forall (h0 (Fin n)))
    exact Filter.Eventually.of_forall (fun _ hx i => hAD (hx i))

theorem grandIntegral_half_moment_le (F : ConfigFamily) {D Cset : Set Space}
    (hD : MeasurableSet D) {c K : ℝ} (hK : 0 < K)
    (hF0 : ∀ (ι : Type) [Fintype ι] (x : ι → Space), 0 ≤ F ι x)
    (hF : GrandFinite F D) (hfull : GrandFinite (momentFamily F Cset c) D)
    (hhalf : GrandFinite (momentFamily F Cset (c/2)) D) :
    grandIntegral (momentFamily F Cset (c/2)) D ≤
      grandIntegral (momentFamily F Cset c) D/(2*K)+(K/2)*grandIntegral F D := by
  let G : ConfigFamily := fun ι _ x => (2*K)⁻¹*momentFamily F Cset c ι x+(K/2)*F ι x
  have hg : GrandFinite G D := (hfull.const_mul _).add (hF.const_mul _)
  have hb := grandIntegral_mono (momentFamily F Cset (c/2)) G hD
    (fun n => hhalf.integrable (Fin n)) (fun n => hg.integrable (Fin n))
    hhalf.summable hg.summable (fun n x _ => ?_)
  swap
  · have hh := mul_le_mul_of_nonneg_left (exp_half_le (u := c*(occupation Cset x)^2) hK)
      (hF0 (Fin n) x)
    simpa only [momentFamily, G, div_mul_eq_mul_div, mul_add, div_eq_mul_inv,
      mul_assoc, mul_comm, mul_left_comm] using hh
  have he : grandIntegral G D = grandIntegral (momentFamily F Cset c) D/(2*K)+
      (K/2)*grandIntegral F D := by
    rw [grandIntegral_add _ _ _ (fun _ => (hfull.const_mul _).integrable _)
      (fun _ => (hF.const_mul _).integrable _) (hfull.const_mul _).summable
      (hF.const_mul _).summable, grandIntegral_const_mul, grandIntegral_const_mul]
    simp only [div_eq_mul_inv]
    ring
  exact hb.trans_eq he

end ContinuumTemperature
end

end OAI
