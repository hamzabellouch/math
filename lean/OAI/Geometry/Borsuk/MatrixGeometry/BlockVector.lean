import Mathlib

namespace OAI

namespace BorsukNine
open scoped BigOperators
section BlockVector
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
noncomputable def blockVector (I : Finset ι) (lam : ℝ) (r : ι → ℝ) (mu : ℝ)
    (z : EuclideanSpace ℝ ↥(Iᶜ : Finset ι)) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i => if hi : i ∈ I then lam * r i else -mu * z ⟨i,Finset.mem_compl.mpr hi⟩)

lemma blockVector_in (I : Finset ι) (lam : ℝ) (r : ι → ℝ) (mu : ℝ)
    (z : EuclideanSpace ℝ ↥(Iᶜ : Finset ι)) {i : ι} (hi : i ∈ I) :
    blockVector I lam r mu z i = lam * r i := by simp [blockVector,hi]
lemma blockVector_out (I : Finset ι) (lam : ℝ) (r : ι → ℝ) (mu : ℝ)
    (z : EuclideanSpace ℝ ↥(Iᶜ : Finset ι)) (i : ↥(Iᶜ : Finset ι)) :
    blockVector I lam r mu z i.val = -mu * z i := by simp [blockVector,Finset.mem_compl.mp i.property]

lemma blockVector_continuous {X : Type*} [TopologicalSpace X] (I : Finset ι)
    {lam mu : X → ℝ} {r : X → ι → ℝ} {z : X → EuclideanSpace ℝ ↥(Iᶜ : Finset ι)}
    (hl : Continuous lam) (hr : Continuous r) (hm : Continuous mu) (hz : Continuous z) :
    Continuous (fun x => blockVector I (lam x) (r x) (mu x) (z x)) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  by_cases hi : i ∈ I
  · simp only [dite_eq_left hi]
    exact hl.mul ((continuous_apply i).comp hr)
  · simp only [dite_eq_right hi]
    let j : ↥(Iᶜ : Finset ι) := ⟨i,Finset.mem_compl.mpr hi⟩
    have hj : Continuous (fun x => z x j) := (PiLp.continuous_apply 2 _ j).comp hz
    exact hm.neg.mul hj

lemma blockVector_continuousOn {X : Type*} [TopologicalSpace X] (I : Finset ι) {S : Set X}
    {lam mu : X → ℝ} {r : X → ι → ℝ} {z : X → EuclideanSpace ℝ ↥(Iᶜ : Finset ι)}
    (hl : ContinuousOn lam S) (hr : ContinuousOn r S) (hm : ContinuousOn mu S) (hz : ContinuousOn z S) :
    ContinuousOn (fun x => blockVector I (lam x) (r x) (mu x) (z x)) S := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  exact blockVector_continuous I (continuousOn_iff_continuous_domRestrict.mp hl)
    (continuousOn_iff_continuous_domRestrict.mp hr) (continuousOn_iff_continuous_domRestrict.mp hm)
    (continuousOn_iff_continuous_domRestrict.mp hz)

lemma blockVector_nonzero {I : Finset ι} (hI : I.Nonempty) {lam mu : ℝ} (hl : 0 < lam)
    {r : ι → ℝ} (hr : ∀ i ∈ I, 0 < r i) (z : EuclideanSpace ℝ ↥(Iᶜ : Finset ι)) :
    blockVector I lam r mu z ≠ 0 := by
  obtain ⟨i,hi⟩ := hI
  intro h
  have he := congrArg (fun v : EuclideanSpace ℝ ι => v i) h
  rw [blockVector_in _ _ _ _ _ hi] at he
  exact (ne_of_gt (mul_pos hl (hr i hi))) he

lemma blockVector_ray {I : Finset ι} {lam mu t : ℝ} (_hl : 0 < lam) (_hm : 0 < mu)
    (hlm : lam + mu = 1) (_ht : 0 < t) {a r : ι → ℝ}
    (hao : ∀ i ∉ I, a i = 0) (hro : ∀ i ∉ I, r i = 0)
    (has : ∑ i, a i = 1) (hrs : ∑ i, r i = 1)
    {b z : EuclideanSpace ℝ ↥(Iᶜ : Finset ι)} (hbs : ∑ i, b i = 1) (hzs : ∑ i, z i = 1)
    (he : blockVector I lam a mu b = t • blockVector I (1/2:ℝ) r (1/2:ℝ) z) :
    t = 1 ∧ lam = 1/2 ∧ mu = 1/2 ∧ a = r ∧ b = z := by
  have hei (i : ι) (hi : i ∈ I) : lam * a i = t * ((1/2:ℝ) * r i) := by
    have h := congrArg (fun v : EuclideanSpace ℝ ι => v i) he
    simpa only [PiLp.smul_apply,smul_eq_mul,blockVector_in _ _ _ _ _ hi] using h
  have heo (i : ↥(Iᶜ : Finset ι)) : -mu * b i = t * (-(1/2:ℝ) * z i) := by
    have h := congrArg (fun v : EuclideanSpace ℝ ι => v i.val) he
    simpa only [PiLp.smul_apply,smul_eq_mul,blockVector_out] using h
  have hia : ∑ i ∈ I, a i = 1 := by
    rw [← has]; exact Finset.sum_subset (Finset.subset_univ I) (fun i _ hi => hao i hi)
  have hir : ∑ i ∈ I, r i = 1 := by
    rw [← hrs]; exact Finset.sum_subset (Finset.subset_univ I) (fun i _ hi => hro i hi)
  have hl' : lam = t*(1/2:ℝ) := by
    have hs := Finset.sum_congr (s₁ := I) (rfl) hei
    simpa only [← Finset.mul_sum,hia,hir,mul_one] using hs
  have hm' : -mu = t*(-(1/2:ℝ)) := by
    have hs := congrArg (fun v : ↥(Iᶜ : Finset ι) → ℝ => ∑ i, v i) (funext heo)
    simpa only [← Finset.mul_sum,hbs,hzs,mul_one] using hs
  have ht1 : t = 1 := by linarith
  have hl2 : lam = 1/2 := by linarith
  have hm2 : mu = 1/2 := by linarith
  refine ⟨ht1,hl2,hm2,?_,?_⟩
  · funext i
    by_cases hi : i ∈ I
    · have h := hei i hi; rw [ht1,hl2] at h; linarith
    · rw [hao i hi,hro i hi]
  · apply PiLp.ext
    intro i
    have h := heo i; rw [ht1,hm2] at h; linarith
end BlockVector
end BorsukNine

end OAI
