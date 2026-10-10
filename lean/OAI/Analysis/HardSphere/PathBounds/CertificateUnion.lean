import Mathlib

namespace OAI

section

section
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators
namespace HardSphere.FreeVisits

lemma largest_fiber {V : Type*} [Fintype V] {q : ℕ} (hq : 0<q) (f : V→Fin q) :
    ∃i : Fin q,Fintype.card V≤q*(Finset.univ.filter (fun v ↦ f v=i)).card := by
  classical
  have hq' : (0:ℝ)<q := by exact_mod_cast hq
  have hf : ∀v∈(Finset.univ : Finset V),f v∈(Finset.univ : Finset (Fin q)) := by simp
  have ht : (Finset.univ : Finset (Fin q)).Nonempty := ⟨⟨0,hq⟩,Finset.mem_univ _⟩
  have hb : (Finset.univ : Finset (Fin q)).card • ((Fintype.card V:ℝ)/(q:ℝ))≤(Finset.univ : Finset V).card := by
    simp only [Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    rw [mul_div_cancel₀ _ hq'.ne']
  obtain ⟨i,hi,h⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to hf ht hb
  refine ⟨i,?_⟩
  have hh := (div_le_iff₀ hq').mp h
  exact_mod_cast hh.trans_eq (mul_comm _ _)

lemma finite_failure_union {W V : Type*} [MeasurableSpace W] [Fintype V]
    (μ : Measure W) {q : ℕ} (hq : 0<q) (bad : Fin q→V→W→Prop)
    {p : ℝ≥0∞} (hp : p≤1)
    (hjoint : ∀i : Fin q,∀A : Finset V,μ {ω | ∀v∈A,bad i v ω}≤p^(q*A.card)) :
    μ {ω | ∀v,∃i,bad i v ω}≤((q:ℝ≥0∞)*p)^(Fintype.card V) := by
  classical
  have hsub : {ω | ∀v,∃i,bad i v ω}⊆⋃f : V→Fin q,{ω | ∀v,bad (f v) v ω} := by
    intro ω hω
    let f : V→Fin q := fun v ↦ Classical.choose (hω v)
    exact mem_iUnion.mpr ⟨f,fun v ↦ Classical.choose_spec (hω v)⟩
  have hf (f : V→Fin q) : μ {ω | ∀v,bad (f v) v ω}≤p^(Fintype.card V) := by
    obtain ⟨i,hi⟩ := largest_fiber hq f
    calc
      _ ≤ μ {ω | ∀v∈Finset.univ.filter (fun v ↦ f v=i),bad i v ω} := by
        apply measure_mono
        intro ω hω v hv
        rw [←(Finset.mem_filter.mp hv).2]
        exact hω v
      _ ≤ p^(q*(Finset.univ.filter (fun v ↦ f v=i)).card) := hjoint i _
      _ ≤ _ := pow_le_pow_right_of_le_one' hp hi
  calc
    _ ≤ μ (⋃f : V→Fin q,{ω | ∀v,bad (f v) v ω}) := measure_mono hsub
    _ ≤ ∑f : V→Fin q,μ {ω | ∀v,bad (f v) v ω} := measure_iUnion_fintype_le _ _
    _ ≤ ∑_f : V→Fin q,p^(Fintype.card V) := Finset.sum_le_sum (fun f _ ↦ hf f)
    _ = _ := by simp [nsmul_eq_mul,mul_pow]

end HardSphere.FreeVisits

end
end

end

end OAI
