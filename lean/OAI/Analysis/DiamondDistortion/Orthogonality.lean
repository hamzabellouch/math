import OAI.Analysis.DiamondDistortion.Ancestry

namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

namespace SegmentSystem
variable {ι κ : Type*} (T : SegmentSystem ι)

lemma primal_sq_le (p : ι →₀ ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hF : ∀ F : T.Family, (∑ i, (∑ v ∈ F.seg i,p v)^2) ≤ M) :
    (T.primalSeminorm p)^2 ≤ M := by
  have hbound : T.primalSeminorm p ≤ Real.sqrt M := by
    rw [primalSeminorm, Seminorm.iSup_apply T.families_bddAbove]
    apply ciSup_le
    intro F
    have h := hF F
    have he : ‖F.test p‖^2 = (∑ i, (∑ v ∈ F.seg i,p v)^2) := by
      rw [EuclideanSpace.norm_sq_eq]
      simp only [Family.test_apply,Real.norm_eq_abs,sq_abs]
    rw [← he, ← Real.sq_sqrt hM] at h
    exact (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp h
  have h := (sq_le_sq₀ (apply_nonneg _ _) (Real.sqrt_nonneg _)).2 hbound
  rwa [Real.sq_sqrt hM] at h

def colorSupport (_T : SegmentSystem ι) (c : ι → κ) (p : ι →₀ ℝ) : Finset κ := p.support.image c

/-- Segment families in disjoint components spend orthogonal testing energies. -/
lemma block_add_sq (c : ι → κ)
    (hsame : ∀ S, T.IsSegment S → ∀ u ∈ S, ∀ v ∈ S, c u=c v)
    (p q : ι →₀ ℝ) (hd : Disjoint (T.colorSupport c p) (T.colorSupport c q)) :
    (T.primalSeminorm (p+q))^2 ≤ (T.primalSeminorm p)^2+(T.primalSeminorm q)^2 := by
  classical
  apply T.primal_sq_le (p+q) (add_nonneg (sq_nonneg _) (sq_nonneg _))
  intro F
  have hz (i : Fin F.n) : (∑ v ∈ F.seg i,p v)*(∑ v ∈ F.seg i,q v)=0 := by
    by_cases hp : (∑ v ∈ F.seg i,p v)=0
    · rw [hp,zero_mul]
    by_cases hq : (∑ v ∈ F.seg i,q v)=0
    · rw [hq,mul_zero]
    obtain ⟨u,hu,hpu⟩ := Finset.exists_ne_zero_of_sum_ne_zero hp
    obtain ⟨v,hv,hqv⟩ := Finset.exists_ne_zero_of_sum_ne_zero hq
    have he := hsame _ (F.allowed i) u hu v hv
    exact False.elim (Finset.disjoint_left.mp hd
      (Finset.mem_image.mpr ⟨u,Finsupp.mem_support_iff.mpr hpu,rfl⟩)
      (Finset.mem_image.mpr ⟨v,Finsupp.mem_support_iff.mpr hqv,he.symm⟩))
  have he (i : Fin F.n) : (∑ v ∈ F.seg i,(p+q) v)^2 =
      (∑ v ∈ F.seg i,p v)^2+(∑ v ∈ F.seg i,q v)^2 := by
    simp only [Finsupp.add_apply,Finset.sum_add_distrib]
    nlinarith [hz i]
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  exact add_le_add
    (T.test_energy_le_allow_empty F.seg (fun i _ => F.allowed i) F.disjoint p)
    (T.test_energy_le_allow_empty F.seg (fun i _ => F.allowed i) F.disjoint q)

/-- A functional on an orthogonal sum is uniformly small outside finitely many
    components. The proof uses finite blocks only, not a reflexivity library. -/
lemma small_color_tail_upper (c : ι → κ)
    (hsame : ∀ S, T.IsSegment S → ∀ u ∈ S, ∀ v ∈ S, c u=c v)
    (x : T.Dual) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : Finset κ, ∀ p : ι →₀ ℝ, (∀ v ∈ p.support, c v ∉ C) →
      x (T.finiteEmbedding p) ≤ ε*T.primalSeminorm p := by
  classical
  by_contra hn
  push Not at hn
  have hchoose (C : Finset κ) : ∃ q : ι →₀ ℝ,
      (∀ v ∈ q.support,c v ∉ C) ∧ T.primalSeminorm q=1 ∧ ε < x (T.finiteEmbedding q) := by
    obtain ⟨p,hout,hval⟩ := hn C
    have hpn0 : T.primalSeminorm p ≠ 0 := by
      intro he
      have hp0 := (T.primal_eq_zero_iff p).mp he
      simp only [hp0,map_zero,mul_zero,lt_self_iff_false] at hval
    have hpn : 0 < T.primalSeminorm p := lt_of_le_of_ne (apply_nonneg _ _) hpn0.symm
    let q := (T.primalSeminorm p)⁻¹ • p
    refine ⟨q, ?_, ?_, ?_⟩
    · intro v hv
      apply hout v
      apply Finsupp.mem_support_iff.mpr
      intro hpv
      have hqv : q v=0 := by simp [q,Finsupp.smul_apply,hpv]
      exact (Finsupp.mem_support_iff.mp hv) hqv
    · simp only [q,map_smul_eq_mul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hpn)]
      exact inv_mul_cancel₀ hpn0
    · simp only [q,map_smul,smul_eq_mul]
      rw [inv_mul_eq_div]
      exact (lt_div_iff₀ hpn).mpr hval
  have hblocks : ∀ n : ℕ, ∃ p : ι →₀ ℝ,
      (T.primalSeminorm p)^2 ≤ (n : ℝ) ∧ (n : ℝ)*ε ≤ x (T.finiteEmbedding p) := by
    intro n
    induction n with
    | zero => exact ⟨0,by simp only [map_zero,zero_pow (by decide : 2 ≠ 0),Nat.cast_zero,le_refl],
        by simp only [map_zero,Nat.cast_zero,zero_mul,le_refl]⟩
    | succ n ih =>
      obtain ⟨p,hpn,hpx⟩ := ih
      obtain ⟨q,hqout,hqn,hqx⟩ := hchoose (T.colorSupport c p)
      have hd : Disjoint (T.colorSupport c p) (T.colorSupport c q) := by
        apply Finset.disjoint_left.mpr
        intro a hap haq
        obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp haq
        exact hqout v hv hap
      refine ⟨p+q, ?_, ?_⟩
      · have h := T.block_add_sq c hsame p q hd
        rw [hqn] at h
        push_cast
        nlinarith
      · simp only [map_add,Nat.cast_add,Nat.cast_one]
        nlinarith
  obtain ⟨n,hn⟩ := exists_nat_gt (‖x‖^2/ε^2)
  have hn0 : (0:ℝ) < n := lt_of_le_of_lt (div_nonneg (sq_nonneg _) (sq_nonneg _)) hn
  have hnε : ‖x‖^2 < (n:ℝ)*ε^2 := (div_lt_iff₀ (sq_pos_of_pos hε)).mp hn
  obtain ⟨p,hpn,hpx⟩ := hblocks n
  have hxb : x (T.finiteEmbedding p) ≤ ‖x‖*T.primalSeminorm p := by
    calc
      _ ≤ ‖x (T.finiteEmbedding p)‖ := Real.le_norm_self _
      _ ≤ ‖x‖*‖T.finiteEmbedding p‖ := x.le_opNorm _
      _ = _ := by rw [T.finiteEmbedding_norm]
  have hprod : (n:ℝ)*ε ≤ ‖x‖*T.primalSeminorm p := hpx.trans hxb
  have hsquare := (sq_le_sq₀ (mul_nonneg hn0.le hε.le)
    (mul_nonneg (norm_nonneg _) (apply_nonneg _ _))).2 hprod
  have hmul := mul_le_mul_of_nonneg_left hpn (sq_nonneg ‖x‖)
  have hcontra := mul_pos hn0 (sub_pos.mpr hnε)
  nlinarith

lemma small_color_tail (c : ι → κ)
    (hsame : ∀ S, T.IsSegment S → ∀ u ∈ S, ∀ v ∈ S, c u=c v)
    (x : T.Dual) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : Finset κ, ∀ p : ι →₀ ℝ, (∀ v ∈ p.support, c v ∉ C) →
      |x (T.finiteEmbedding p)| ≤ ε*T.primalSeminorm p := by
  obtain ⟨C,hC⟩ := T.small_color_tail_upper c hsame x hε
  refine ⟨C,?_⟩
  intro p hp
  apply abs_le.mpr
  refine ⟨?_,hC p hp⟩
  have h := hC (-p) (by simpa only [Finsupp.support_neg] using hp)
  simp only [map_neg,map_neg_eq_map] at h
  linarith

/-- No nonzero coordinate is lost by using the actual Finsupp support. -/
lemma sum_sq_le_support (p : ι →₀ ℝ) (S : Finset ι) :
    (∑ v ∈ S,p v^2) ≤ ∑ v ∈ p.support,p v^2 := by
  classical
  have h : (∑ v ∈ S,p v^2) ≤ ∑ v ∈ S ∪ p.support,p v^2 :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (fun _ _ _ => sq_nonneg _)
  have he : (∑ v ∈ p.support,p v^2) = ∑ v ∈ S ∪ p.support,p v^2 := by
    apply Finset.sum_subset Finset.subset_union_right
    intro v _ hv
    rw [Finsupp.notMem_support_iff.mp hv]
    norm_num
  exact h.trans_eq he.symm

lemma coordinate_energy_le (p : ι →₀ ℝ) (S : Finset ι) :
    (∑ v ∈ S,p v^2) ≤ (T.primalSeminorm p)^2 := by
  classical
  have h := T.test_energy_le (fun v : S => {v.val}) (fun v => T.singleton v.val)
    (by
      intro v w hvw
      exact Finset.disjoint_singleton.mpr (fun he => hvw (Subtype.ext he))) p
  simp only [Finset.sum_singleton] at h
  calc
    _ = ∑ v : S,p v.val^2 := (Finset.sum_coe_sort S (fun v => p v^2)).symm
    _ ≤ _ := h

lemma primal_sq_le_of_segment (p : ι →₀ ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hS : ∀ S, T.IsSegment S → (∑ v ∈ S,p v)^2 ≤ L*(∑ v ∈ S,p v^2)) :
    (T.primalSeminorm p)^2 ≤ L*(∑ v ∈ p.support,p v^2) := by
  classical
  apply T.primal_sq_le p (mul_nonneg hL (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  intro F
  have he : (∑ i,∑ v ∈ F.seg i,p v^2) = ∑ v ∈ Finset.univ.biUnion F.seg,p v^2 := by
    symm
    apply Finset.sum_biUnion
    intro i _ j _ hij
    exact F.disjoint hij
  calc
    _ ≤ ∑ i,L*(∑ v ∈ F.seg i,p v^2) := Finset.sum_le_sum (fun i _ => hS _ (F.allowed i))
    _ = L*(∑ v ∈ Finset.univ.biUnion F.seg,p v^2) := by rw [← Finset.mul_sum,he]
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_sq_le_support p _) hL

def finiteArray (S : Finset ι) (a : ι → ℝ) : ι →₀ ℝ :=
  ∑ v ∈ S,a v • Finsupp.single v 1

lemma finiteArray_apply (S : Finset ι) (a : ι → ℝ) (v : ι) :
    finiteArray S a v = if v ∈ S then a v else 0 := by
  classical
  simp [finiteArray,Finsupp.finsetSum_apply,Finsupp.single_apply,Finset.sum_ite_eq']

lemma finiteArray_support (S : Finset ι) (a : ι → ℝ) : (finiteArray S a).support ⊆ S := by
  intro v hv
  by_contra hn
  exact (Finsupp.mem_support_iff.mp hv) (by rw [finiteArray_apply,ite_eq_right hn])

lemma finiteArray_energy (S : Finset ι) (a : ι → ℝ) :
    (∑ v ∈ (finiteArray S a).support,finiteArray S a v^2) = ∑ v ∈ S,a v^2 := by
  calc
    _ = ∑ v ∈ S,finiteArray S a v^2 := by
      apply Finset.sum_subset (finiteArray_support S a)
      intro v _ hv
      rw [Finsupp.notMem_support_iff.mp hv]
      norm_num
    _ = _ := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [finiteArray_apply,ite_eq_left hv]

lemma finiteArray_pairing (S : Finset ι) (a : ι → ℝ) (x : T.Dual) :
    x (T.finiteEmbedding (finiteArray S a)) = ∑ v ∈ S,a v*x (T.unitVector v) := by
  simp only [finiteArray,map_sum,map_smul,finiteEmbedding_single,one_smul,smul_eq_mul]

/-- Bounded nonnegative finite square sums have uniformly small disjoint tails.
    This is proved directly from a real supremum, with no countability assumption. -/
lemma finite_square_tails (a : ι → ℝ) {M : ℝ}
    (hM : ∀ S : Finset ι,(∑ v ∈ S,a v^2) ≤ M) {δ : ℝ} (hδ : 0 < δ) :
    ∃ S : Finset ι, ∀ U : Finset ι, Disjoint S U → (∑ v ∈ U,a v^2) < δ := by
  classical
  let E : Set ℝ := Set.range (fun S : Finset ι => ∑ v ∈ S,a v^2)
  have hEb : BddAbove E := ⟨M,by rintro _ ⟨S,rfl⟩; exact hM S⟩
  have hEn : E.Nonempty := ⟨0,∅,by simp⟩
  obtain ⟨b,⟨S,rfl⟩,hS⟩ := exists_lt_of_lt_csSup hEn (sub_lt_self (sSup E) hδ)
  refine ⟨S,?_⟩
  intro U hU
  have h := le_csSup hEb (show (∑ v ∈ S ∪ U,a v^2) ∈ E from ⟨S ∪ U,rfl⟩)
  rw [Finset.sum_union hU] at h
  linarith

end SegmentSystem

end DiamondDistortion

end

end OAI
