import OAI.Combinatorics.SparsestCut.WeightedMetric

namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.LabelCount
open scoped BigOperators RealInnerProductSpace
open UniformSparsestCut
variable {m N : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)

def signature (B : ℤ) (l : Fin N → ℤ) : Finset (Fin N × ↥(Finset.Icc (-B) B)) :=
  Finset.univ.filter (fun p => p.2.val ≤ l p.1)

lemma signature_injective (B : ℤ) (A : Finset (Fin N → ℤ))
    (hA : ∀ l ∈ A, ∀ i, l i ∈ Finset.Icc (-B) B) :
    Set.InjOn (signature B) (↑A : Set (Fin N → ℤ)) := by
  intro l hl k hk he
  funext i
  apply le_antisymm
  · have hm : (i,⟨l i,hA l hl i⟩) ∈ signature B l := by simp [signature]
    rw [he] at hm
    simpa [signature] using hm
  · have hm : (i,⟨k i,hA k hk i⟩) ∈ signature B k := by simp [signature]
    rw [← he] at hm
    simpa [signature] using hm

lemma regular_floor_iff (u : Fin N → E) {τ : ℝ} (hτ : 0 < τ)
    {θ : E} (hθ : RoundedCharts.regular u τ θ) (i : Fin N) (k : ℤ) :
    k ≤ RoundedCharts.integerLabel u τ θ i ↔ (k:ℝ)*τ < inner ℝ (u i) θ := by
  rw [RoundedCharts.integerLabel, Int.le_floor]
  rw [le_div_iff₀ hτ]
  exact ⟨fun h => lt_of_le_of_ne h (Ne.symm (hθ i k)), le_of_lt⟩

def affineForm (u : Fin N → E) (τ : ℝ) (B : ℤ)
    (p : Fin N × ↥(Finset.Icc (-B) B)) : E × ℝ →ₗ[ℝ] ℝ :=
  (innerSL ℝ (u p.1)).toLinearMap.comp (LinearMap.fst ℝ E ℝ) -
    ((p.2.val:ℝ)*τ) • LinearMap.snd ℝ E ℝ

lemma label_count (u : Fin N → E) {τ : ℝ} (hτ : 0 < τ) (B : ℤ)
    (A : Finset (Fin N → ℤ))
    (hb : ∀ l ∈ A, ∀ i, l i ∈ Finset.Icc (-B) B)
    (hA : ∀ l ∈ A, ∃ θ : E, RoundedCharts.regular u τ θ ∧ RoundedCharts.integerLabel u τ θ = l) :
    A.card ≤ ∑ j ∈ Finset.Iic (m+1), (N*(Finset.Icc (-B) B).card).choose j := by
  let P := A.image (signature B)
  have hP : ∀ p ∈ P, ∃ θ : E × ℝ, ∀ i,
      affineForm u τ B i θ ≠ 0 ∧ (0 < affineForm u τ B i θ ↔ i ∈ p) := by
    intro p hp
    obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨θ,hr,hθ⟩ := hA l hl
    refine ⟨(θ,1),?_⟩
    intro i
    have he : affineForm u τ B i (θ,1) = inner ℝ (u i.1) θ-(i.2.val:ℝ)*τ := by
      simp [affineForm]
    rw [he]
    refine ⟨sub_ne_zero.mpr (hr _ _),?_⟩
    rw [sub_pos, ← regular_floor_iff u hτ hr,hθ]
    simp [signature]
  have hc := HyperplaneCount.sign_patterns_bound (affineForm u τ B) P hP
  have hdim : Module.finrank ℝ (E × ℝ) = m+1 := by simp [Module.finrank_prod]
  have hcard : Fintype.card (Fin N × ↥(Finset.Icc (-B) B)) = N*(Finset.Icc (-B) B).card := by simp
  rw [hdim,hcard] at hc
  rwa [Finset.card_image_of_injOn (signature_injective B A hb)] at hc

end UniformSparsestCut.LabelCount

namespace UniformSparsestCut.LabelCount
open scoped BigOperators
noncomputable section
lemma power_sum_le (H d : ℕ) : (∑ j∈Finset.range (d+1), H^j)≤(H+1)^d := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Finset.sum_range_succ]
    calc
      _ ≤ (H+1)^d+H^(d+1) := Nat.add_le_add_right ih _
      _ ≤ (H+1)^d+(H+1)^d*H := by
        rw [pow_succ]
        gcongr
        omega
      _ = (H+1)^(d+1) := by ring
lemma binomial_sum_le (H d : ℕ) : (∑ j∈Finset.Iic d, H.choose j)≤(H+1)^d := by
  have he : Finset.Iic d=Finset.range (d+1) := by ext j; simp
  rw [he]
  exact (Finset.sum_le_sum (fun j _ => Nat.choose_le_pow H j)).trans (power_sum_le H d)
variable {m N S : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)
lemma vertex_count (u : Fin S → Fin N → E) {τ : ℝ} (hτ : 0<τ)
    [Fintype (RoundedCharts.Vertex u τ)] (B : ℤ)
    (hb : ∀ v : RoundedCharts.Vertex u τ, ∀ i, v.val.2 i∈Finset.Icc (-B) B) :
    Fintype.card (RoundedCharts.Vertex u τ)≤S*(N*(Finset.Icc (-B) B).card+1)^(m+1) := by
  classical
  let T (s : Fin S) := Finset.univ.filter (fun v : RoundedCharts.Vertex u τ => v.val.1=s)
  let A (s : Fin S) := (T s).image (fun v => v.val.2)
  have hcard (s : Fin S) : (T s).card=(A s).card := by
    apply (Finset.card_image_of_injOn _).symm
    intro v hv w hw h
    apply Subtype.ext
    apply Prod.ext
    · exact (Finset.mem_filter.mp hv).2.trans (Finset.mem_filter.mp hw).2.symm
    · exact h
  have hs (s : Fin S) : (T s).card≤(N*(Finset.Icc (-B) B).card+1)^(m+1) := by
    rw [hcard]
    apply (label_count (u s) hτ B (A s) ?_ ?_).trans (binomial_sum_le _ _)
    · intro l hl i
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hl
      exact hb v i
    · intro l hl
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hl
      obtain ⟨θ,hθ,hr,hl⟩ := v.property
      have he : v.val.1=s := (Finset.mem_filter.mp hv).2
      exact ⟨θ,by simpa only [← he] using hr,by simpa only [← he] using hl⟩
  calc
    _ = ∑ s, (T s).card := by
      simpa only [Finset.card_univ] using (Finset.card_eq_sum_card_fiberwise
        (f := fun v : RoundedCharts.Vertex u τ => v.val.1)
        (s := Finset.univ) (t := Finset.univ) (fun _ _ => Finset.mem_univ _))
    _ ≤ ∑ _s : Fin S, (N*(Finset.Icc (-B) B).card+1)^(m+1) := Finset.sum_le_sum (fun s _ => hs s)
    _ = _ := by simp
end
end UniformSparsestCut.LabelCount

end

end OAI
