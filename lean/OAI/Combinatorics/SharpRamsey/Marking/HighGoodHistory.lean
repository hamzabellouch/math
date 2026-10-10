import Mathlib
import OAI.Combinatorics.SharpRamsey.Marking.AtomEscape
import OAI.Combinatorics.SharpRamsey.Windows.GoodPopulation
import OAI.Combinatorics.SharpRamsey.Exposure.ZeroExposure

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset Real ExposureModel
open scoped Classical BigOperators
noncomputable section
local instance flat_ActualHighGoodHistory_1 (w : ℕ) : DecidableEq (Block w) := Classical.decEq _
variable {Ω Θ β : Type} [Fintype Ω] [Fintype Θ] [Fintype β]

lemma one_goodMiddle_count (n k : ℕ) (p : Law Ω) (θ : Ω→Θ)
    (G : Ω→Slot 1 (n+k)→β) (t : Fin k)
    (z : (model 1 n k p θ G t).FreshHistory)
    (bad : Finset ((model 1 n k p θ G t).Index z.1)) :
    2*(n+k)≤(goodMiddle 1 n k p θ G t z bad 0).card+bad.card := by
  have h:=goodPopulation_predeletion 1 n k p θ G t z bad ∅
  simpa using h

theorem high_good_history_half (n k : ℕ) (hn : 0<n) (hkn : k≤n)
    (p : Law Ω) (θ : Ω→Θ) (G : Ω→Slot 1 (n+k)→β) (t : Fin k)
    (hp : ∀ z,0<(model 1 n k p θ G t).remaining z)
    (bad : ∀ z : (model 1 n k p θ G t).FreshHistory,
      Finset ((model 1 n k p θ G t).Index z.1)) (A : ℝ)
    (hb : (∑ z,((model 1 n k p θ G t).freshLaw hp).mass z*((bad z).card:ℝ))≤A)
    (hs : (n:ℝ)*(∑ z,((model 1 n k p θ G t).freshLaw hp).mass z*
      (((model 1 n k p θ G t).freshSelected z∩bad z).card:ℝ))≤A)
    (hA : A≤(2*(n+k):ℕ)/20) :
    (1:ℝ)/2≤((model 1 n k p θ G t).freshLaw hp).event
      (univ.filter (fun z=>(model 1 n k p θ G t).representative z (0,false)∉bad z ∧
        ((2*(n+k):ℕ):ℝ)/2≤(goodMiddle 1 n k p θ G t z (bad z) 0).card)) := by
  let M:=model 1 n k p θ G t
  let μ:=M.freshLaw hp
  let N : ℕ:=2*(n+k)
  let f:=fun z : M.FreshHistory=>((bad z).card:ℝ)
  let g:=fun z : M.FreshHistory=>((M.freshSelected z∩bad z).card:ℝ)
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  have hN : (0:ℝ)<N := by dsimp [N]; positivity
  have hNn : (N:ℝ)≤4*n := by
    exact_mod_cast (by dsimp [N]; omega : N≤4*n)
  have hs' : (∑ z,μ.mass z*g z)≤A/n := by
    apply (le_div_iff₀ hn0).mpr
    simpa only [mul_comm] using hs
  have hprob:=SimultaneousExtraction.simultaneous_mass μ.mass μ.nonneg μ.total f g
    (fun z=>Nat.cast_nonneg _) (fun z=>Nat.cast_nonneg _) A (A/n) ((N:ℝ)/2) (1/2)
    (by positivity) (by norm_num) hb hs'
  have hA0 : 0≤A := (sum_nonneg (fun z _=>mul_nonneg (μ.nonneg z) (by positivity))).trans hb
  have hleft : (1:ℝ)/2≤1-A/((N:ℝ)/2)-(A/n)/(1/2) := by
    have h1 : A/((N:ℝ)/2)≤1/10 := by
      apply (div_le_iff₀ (by positivity : 0<(N:ℝ)/2)).mpr
      change A≤(N:ℝ)/20 at hA
      linarith
    have h2 : (A/n)/(1/2)≤2/5 := by
      apply (div_le_iff₀ (by norm_num : (0:ℝ)<1/2)).mpr
      apply (div_le_iff₀ hn0).mpr
      change A≤(N:ℝ)/20 at hA
      linarith
    linarith
  apply (hleft.trans hprob).trans
  apply Law.event_mono
  intro z hz
  obtain ⟨hf,hg⟩:=(mem_filter.mp hz).2
  have hg0 : (M.freshSelected z∩bad z).card=0 := by
    have hlt : ((M.freshSelected z∩bad z).card:ℝ)<1 := by dsimp [g] at hg; linarith
    have : (M.freshSelected z∩bad z).card<1 := by exact_mod_cast hlt
    omega
  apply mem_filter.mpr
  refine ⟨mem_univ _,?_,?_⟩
  · intro hrep
    have hr : M.representative z (0,false)∈M.freshSelected z := by
      rw [←representative_selected]
      exact mem_map.mpr ⟨(0,false),mem_univ _,rfl⟩
    have hi:=mem_inter.mpr ⟨hr,hrep⟩
    rw [card_eq_zero.mp hg0] at hi
    simp at hi
  · have hc:=one_goodMiddle_count n k p θ G t z (bad z)
    have hc' : (N:ℝ)≤(goodMiddle 1 n k p θ G t z (bad z) 0).card+f z := by
      dsimp only [N, f]
      exact_mod_cast hc
    linarith
end
end SharpLogRamsey.Selection.Windows

end

end OAI
