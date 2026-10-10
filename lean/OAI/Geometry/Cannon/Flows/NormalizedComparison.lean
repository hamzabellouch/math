import Mathlib
import OAI.Geometry.Cannon.ScalarLimits.Words

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
section
open Set Topology
open Set MeasureTheory
open scoped BigOperators
open scoped NNReal ENNReal
open Set Metric
open Set Filter Topology
open Set Filter Topology Metric
open Set Metric Topology
open Set unitInterval

namespace CannonSecondMagnification

open Filter Topology Metric CannonVariation

theorem normalized_comparison {X : Type*} [TopologicalSpace X]
    (W : ℕ → X → ℝ) (p : ℕ → X) (A sig : ℕ → ℝ)
    (hsig : ∀ i, sig i ≠ 0)
    (hc : ∀ i j, p i ≠ p j → ∀ x, x ≠ p i → x ≠ p j →
      NonconstantAt (W i) x → W j x = W j (p i)) :
    ∀ i j, p i ≠ p j → ∀ x, x ≠ p i → x ≠ p j →
      NonconstantAt (fun z => (W i z - A i) / sig i) x →
      (W j x - A j) / sig j = (W j (p i) - A j) / sig j := by
  intro i j hij x hxi hxj hx
  rw [hc i j hij x hxi hxj ((nonconstantAt_normalize _ _ _ (hsig i) _).mp hx)]

theorem impossible_nonconstant_limit {X : Type*} [MetricSpace X]
    (F : ℕ → X → ℝ) (p : ℕ → X) (b : X) (W : X → ℝ)
    (hp : Tendsto p atTop (𝓝 b)) (hinj : Function.Injective p)
    (hW : ContinuousOn W ({b}ᶜ : Set X))
    (hlim : ∀ K : Set X, IsCompact K → b ∉ K → TendstoUniformlyOn F W atTop K)
    (hcomp : ∀ i j, p i ≠ p j → ∀ x, x ≠ p i → x ≠ p j →
      NonconstantAt (F i) x → F j x = F j (p i))
    {v w : X} (q : Path v w) (hqb : b ∉ range q) (hvar : W v < W w) : False := by
  let d := (W w - W v) / 5
  have hd : 0 < d := div_pos (sub_pos.mpr hvar) (by norm_num)
  have hWr : ContinuousOn W (range q) := hW.mono (by
    intro x hx hxb
    exact hqb (hxb ▸ hx))
  obtain ⟨v₁,w₁,q₁,hq₁,hv₁,hw₁,hW₁⟩ := value_subpath W q hWr
    (W v + d) (W v + 2*d) (by linarith) (by linarith) (by dsimp [d]; linarith)
  obtain ⟨v₂,w₂,q₂,hq₂,hv₂,hw₂,hW₂⟩ := value_subpath W q hWr
    (W v + 3*d) (W v + 4*d) (by linarith) (by linarith) (by dsimp [d]; linarith)
  let K := range q₁ ∪ range q₂
  have hK : IsCompact K := (isCompact_range q₁.continuous).union (isCompact_range q₂.continuous)
  have hbK : b ∉ K := by
    rintro (hb | hb)
    · exact hqb (hq₁ hb)
    · exact hqb (hq₂ hb)
  have havoid : ∀ᶠ n in atTop, p n ∉ K := hp.eventually (hK.isClosed.isOpen_compl.mem_nhds hbK)
  have he : ∀ᶠ n in atTop, ∀ z ∈ K, |W z - F n z| < d/4 := by
    simpa only [Real.dist_eq] using (Metric.tendstoUniformlyOn_iff.mp (hlim K hK hbK) (d/4) (by positivity))
  obtain ⟨N,hN⟩ := eventually_atTop.1 (havoid.and he)
  let i := N
  let j := N+1
  have hi := hN i le_rfl
  have hj := hN j (Nat.le_succ N)
  have hv₁K : v₁ ∈ K := Or.inl (q₁.source_mem_range)
  have hw₁K : w₁ ∈ K := Or.inl (q₁.target_mem_range)
  have hv₂K : v₂ ∈ K := Or.inr (q₂.source_mem_range)
  have hw₂K : w₂ ∈ K := Or.inr (q₂.target_mem_range)
  have hi₁ : F i v₁ < F i w₁ := by
    have ha := (abs_lt.mp (hi.2 v₁ hv₁K))
    have hb := (abs_lt.mp (hi.2 w₁ hw₁K))
    rw [hv₁] at ha
    rw [hw₁] at hb
    linarith
  have hi₂ : F i v₂ < F i w₂ := by
    have ha := (abs_lt.mp (hi.2 v₂ hv₂K))
    have hb := (abs_lt.mp (hi.2 w₂ hw₂K))
    rw [hv₂] at ha
    rw [hw₂] at hb
    linarith
  obtain ⟨z₁,hz₁,hz₁var⟩ := path_meets_variation (F i) q₁ hi₁.ne
  obtain ⟨z₂,hz₂,hz₂var⟩ := path_meets_variation (F i) q₂ hi₂.ne
  have hz₁K : z₁ ∈ K := Or.inl hz₁
  have hz₂K : z₂ ∈ K := Or.inr hz₂
  have hpi : p i ≠ p j := fun h => (Nat.ne_add_one N) (hinj h)
  have he₁ := hcomp i j hpi z₁ (fun h => hi.1 (h ▸ hz₁K)) (fun h => hj.1 (h ▸ hz₁K)) hz₁var
  have he₂ := hcomp i j hpi z₂ (fun h => hi.1 (h ▸ hz₂K)) (fun h => hj.1 (h ▸ hz₂K)) hz₂var
  have heq : F j z₁ = F j z₂ := he₁.trans he₂.symm
  have hb₁ := (hW₁ z₁ hz₁).2
  have hb₂ := (hW₂ z₂ hz₂).1
  have ha := abs_lt.mp (hj.2 z₁ hz₁K)
  have hb := abs_lt.mp (hj.2 z₂ hz₂K)
  linarith

end CannonSecondMagnification

end
end
end
end
end
end
end
end
end
end

end OAI
