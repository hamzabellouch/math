import OAI.NumberTheory.DirichletL.PrimeRows.RowPartition

namespace OAI

noncomputable section
open scoped Classical BigOperators
open Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical

def smallDyadicIndices (L : ℝ) : Finset ℕ :=
  (Finset.range (Nat.find (pow_unbounded_of_one_lt L (by norm_num : (1:ℝ)<2)))).filter (fun n=>(2:ℝ)^n≤L)

@[simp] lemma mem_smallDyadicIndices {L : ℝ} {n : ℕ} : n∈smallDyadicIndices L ↔ (2:ℝ)^n≤L := by
  simp only [smallDyadicIndices,Finset.mem_filter,Finset.mem_range]
  constructor
  · exact And.right
  · intro hn
    refine ⟨?_,hn⟩
    by_contra h
    have hp := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (not_lt.mp h)
    exact not_lt_of_ge (hp.trans hn) (Nat.find_spec (pow_unbounded_of_one_lt L (by norm_num : (1:ℝ)<2)))

def smallDyadicRows (L : ℝ) (n : ℕ) : Finset FreeRow := (dyadicRows 1 n).filter (fun u=>rowNorm u<L)

@[simp] lemma mem_smallDyadicRows {L : ℝ} {n : ℕ} {u : FreeRow} :
    u∈smallDyadicRows L n ↔ u∈dyadicRows 1 n ∧ rowNorm u<L := Finset.mem_filter

lemma smallDyadicRows_disjoint (L : ℝ) : Pairwise (fun m n=>Disjoint (smallDyadicRows L m) (smallDyadicRows L n)) := by
  intro m n hmn
  exact (dyadicRows_disjoint 1 (by norm_num) hmn).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)

lemma smallDyadicRows_eq_empty {L : ℝ} {n : ℕ} (hn : n∉smallDyadicIndices L) : smallDyadicRows L n=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro u hu
  have h := mem_smallDyadicRows.mp hu
  have hlo := (mem_dyadicRows.mp h.1).2.1
  apply hn
  rw [mem_smallDyadicIndices]
  simpa only [one_mul] using hlo.trans h.2.le

lemma small_rows_biUnion (L : ℝ) :
    (smallDyadicIndices L).biUnion (smallDyadicRows L)=rowBand 1 L := by
  ext u
  constructor
  · intro hu
    obtain ⟨n,hn,hu⟩ := Finset.mem_biUnion.mp hu
    have hh := mem_smallDyadicRows.mp hu
    have hm := mem_dyadicRows.mp hh.1
    exact mem_rowBand.mpr ⟨hm.1,rowNorm_ge_one u,hh.2⟩
  · intro hu
    have hh := mem_rowBand.mp hu
    obtain ⟨n,hn⟩ := exists_dyadicRows 1 (by norm_num) u hh.1 hh.2.1
    refine Finset.mem_biUnion.mpr ⟨n,?_,mem_smallDyadicRows.mpr ⟨hn,hh.2.2⟩⟩
    rw [mem_smallDyadicIndices]
    have hlo := (mem_dyadicRows.mp hn).2.1
    simpa only [one_mul] using hlo.trans hh.2.2.le

lemma sum_small_dyadicRows (L : ℝ) (f : FreeRow→ℂ) :
    (∑u∈rowBand 1 L,f u)=∑n∈smallDyadicIndices L,∑u∈smallDyadicRows L n,f u := by
  rw [←small_rows_biUnion L]
  exact Finset.sum_biUnion (fun m hm n hn hmn=>smallDyadicRows_disjoint L hmn)

end SevenEighths.ProbeHighRowFamily

end

end OAI
