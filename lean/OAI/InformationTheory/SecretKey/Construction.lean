import OAI.InformationTheory.SecretKey.MatrixBasics

namespace OAI

noncomputable section

open Matrix

open scoped MatrixOrder ComplexOrder Kronecker

namespace ZeroKey

section

universe v1102_0 v1102_1

variable {σ : Type v1102_0} {ι : σ → Type v1102_1} [inst1102_0 : Fintype σ] [inst1102_1 : DecidableEq σ]
  [inst1102_2 : ∀ s, Fintype (ι s)] [inst1102_3 : ∀ s, DecidableEq (ι s)]

omit inst1102_3 in
lemma tensorPi_trace [∀ s, DecidableEq (ι s)] (A : ∀ s, Matrix (ι s) (ι s) ℂ) :
    trace (tensorPi A) = ∏ s, trace (A s) := by
  simp only [Matrix.trace, Matrix.diag, tensorPi]
  exact (Fintype.prod_sum (fun s i => A s i i)).symm

lemma tensorPi_trace_mul (A B : ∀ s, Matrix (ι s) (ι s) ℂ) :
    trace (tensorPi A * tensorPi B) = ∏ s, trace (A s * B s) := by
  rw [← tensorPi_mul, tensorPi_trace]

lemma tensorPi_commute (A B : ∀ s, Matrix (ι s) (ι s) ℂ)
    (h : ∀ s, Commute (A s) (B s)) : Commute (tensorPi A) (tensorPi B) := by
  change tensorPi A * tensorPi B = tensorPi B * tensorPi A
  rw [← tensorPi_mul, ← tensorPi_mul]
  congr 1
  funext s
  exact (h s).eq

end

section

namespace Explicit

def constructionMap : Matrix Basis Basis ℂ →ₗ[ℂ] Matrix Label Label ℂ := traceBlockMap block

lemma contextParity_sq (t : Fin 6) : contextParity t * contextParity t = 1 := by
  unfold contextParity
  split <;> norm_num

lemma contextEigenvalue_product (t : Fin 6) (a : Outcome) :
    ∏ j, contextEigenvalue t a j = contextParity t := by
  rw [Fin.prod_univ_three]
  change signValue (ofLex a).1 * signValue (ofLex a).2 *
    (contextParity t * signValue (ofLex a).1 * signValue (ofLex a).2) = _
  calc
    _ = contextParity t * (signValue (ofLex a).1 * signValue (ofLex a).1) *
      (signValue (ofLex a).2 * signValue (ofLex a).2) := by ring
    _ = _ := by rw [signValue_sq, signValue_sq, mul_one, mul_one]

lemma context_shared (r c : Fin 3) :
    contextObservable (Fin.castAdd 3 r) c = contextObservable (Fin.natAdd 3 c) r := by
  fin_cases r <;> fin_cases c <;> rfl

theorem magic_parity (a : Fin 6 → Outcome) :
    ¬∀ t s, t≠s → 0 < (Matrix.trace (contextProjection t (a t) *
      contextProjection s (a s))).re := by
  intro hp
  have ha (r c : Fin 3) :
      contextEigenvalue (Fin.castAdd 3 r) (a (Fin.castAdd 3 r)) c =
        contextEigenvalue (Fin.natAdd 3 c) (a (Fin.natAdd 3 c)) r := by
    have ht : Fin.castAdd 3 r ≠ Fin.natAdd 3 c := by
      fin_cases r <;> fin_cases c <;> decide
    have hpos := hp _ _ ht
    have hn : contextProjection (Fin.castAdd 3 r) (a (Fin.castAdd 3 r)) *
        contextProjection (Fin.natAdd 3 c) (a (Fin.natAdd 3 c)) ≠ 0 := by
      intro hz
      rw [hz, Matrix.trace_zero] at hpos
      exact (lt_irrefl 0 hpos)
    apply eigenvalues_agree _ _ (contextObservable (Fin.castAdd 3 r) c) _ _
      (context_eigen_right _ _ _) ?_ hn
    rw [context_shared]
    exact context_eigen _ _ _
  have hr : (∏ r : Fin 3, ∏ c : Fin 3,
      contextEigenvalue (Fin.castAdd 3 r) (a (Fin.castAdd 3 r)) c) = 1 := by
    simp only [contextEigenvalue_product]
    rw [Fin.prod_univ_three]
    norm_num [contextParity, Fin.ext_iff]
  have hc : (∏ c : Fin 3, ∏ r : Fin 3,
      contextEigenvalue (Fin.natAdd 3 c) (a (Fin.natAdd 3 c)) r) = -1 := by
    simp only [contextEigenvalue_product]
    rw [Fin.prod_univ_three]
    norm_num [contextParity, Fin.ext_iff]
  have he : (1:ℂ) = -1 := by
    calc
      1 = ∏ r : Fin 3, ∏ c : Fin 3,
          contextEigenvalue (Fin.castAdd 3 r) (a (Fin.castAdd 3 r)) c := hr.symm
      _ = ∏ c : Fin 3, ∏ r : Fin 3,
          contextEigenvalue (Fin.natAdd 3 c) (a (Fin.natAdd 3 c)) r := by
        simp_rw [ha]
        exact Finset.prod_comm
      _ = -1 := hc
  norm_num at he

lemma sum_basis (f : Basis → ℂ) : ∑ i, f i = ∑ i : EightSet → LocalBasis, f (toLex i) := by
  exact (Equiv.sum_comp (show (EightSet → LocalBasis) ≃ Basis from Equiv.refl _) f).symm

lemma projection_trace_mul (i j : Label) :
    trace (projection i * projection j) = ∏ S, trace
      (localProjection S (ofLex i).1 (ofLex (ofLex i).2 S) *
        localProjection S (ofLex j).1 (ofLex (ofLex j).2 S)) := by
  let e : Basis ≃ (EightSet → LocalBasis) := Equiv.refl _
  let A := tensorPi (fun S => localProjection S (ofLex i).1 (ofLex (ofLex i).2 S))
  let B := tensorPi (fun S => localProjection S (ofLex j).1 (ofLex (ofLex j).2 S))
  change trace (A.submatrix e e * B.submatrix e e) = _
  rw [Matrix.submatrix_mul_equiv]
  change (∑ h : Basis, (A * B) (ofLex h) (ofLex h)) = _
  rw [sum_basis]
  exact tensorPi_trace_mul _ _

lemma projection_orthogonal (q : Question) (a b : OutcomeString) (hab : a≠b) :
    projection (toLex (q,a)) * projection (toLex (q,b)) = 0 := by
  have hab' : ofLex a ≠ ofLex b := by
    intro h
    exact hab ((show OutcomeString ≃ (EightSet → Outcome) from Equiv.refl _).injective h)
  obtain ⟨S,hS⟩ := Function.ne_iff.mp hab'
  ext h l
  apply (projection_mul_apply (i := (toLex (q,a) : Label)) (j := (toLex (q,b) : Label)) h l).trans
  apply Finset.prod_eq_zero (Finset.mem_univ S)
  change (localProjection S q (ofLex a S) * localProjection S q (ofLex b S)) _ _ = 0
  rw [localProjection_orthogonal S q _ _ hS]
  rfl

universe v1803_0

lemma trace_product_nonneg {ι : Type v1803_0} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ trace (A*B) := by
  have hh := (hB.mul_mul_conjTranspose_same (CFC.sqrt A)).trace_nonneg
  rwa [(CFC.sqrt_nonneg A).posSemidef.isHermitian.eq, trace_mul_cycle,
    CFC.sqrt_mul_sqrt_self A hA.nonneg] at hh

lemma local_trace_pos_of_global (i j : Label)
    (h : 0 < (trace (projection i * projection j)).re) (S : EightSet) :
    0 < (trace (localProjection S (ofLex i).1 (ofLex (ofLex i).2 S) *
      localProjection S (ofLex j).1 (ofLex (ofLex j).2 S))).re := by
  have hnn := trace_product_nonneg (localProjection_projection S (ofLex i).1 (ofLex (ofLex i).2 S)).nonneg.posSemidef
    (localProjection_projection S (ofLex j).1 (ofLex (ofLex j).2 S)).nonneg.posSemidef
  have hn : trace (localProjection S (ofLex i).1 (ofLex (ofLex i).2 S) *
      localProjection S (ofLex j).1 (ofLex (ofLex j).2 S)) ≠ 0 := by
    intro hz
    rw [projection_trace_mul, Finset.prod_eq_zero (Finset.mem_univ S) hz] at h
    exact lt_irrefl 0 h
  have hpair := RCLike.nonneg_iff.mp hnn
  apply lt_of_le_of_ne hpair.1
  intro hz
  apply hn
  apply Complex.ext
  · exact hz.symm
  · exact hpair.2

end Explicit

open Finset

section BooleanFunctions

universe v1836_0 v1836_1

variable {α : Type v1836_0} {𝕜 : Type v1836_1} [inst1836_0 : Fintype α] [inst1836_1 : DecidableEq α] [inst1836_2 : Field 𝕜]

def booleanMonomial (S : Finset α) : Finset α → 𝕜 :=
  fun B => if S ⊆ B then 1 else 0

def booleanDegreeSpace (d : ℕ) : Submodule 𝕜 (Finset α → 𝕜) :=
  Submodule.span 𝕜 (Set.range (fun S : {S : Finset α // S.card ≤ d} => booleanMonomial S.1))

omit inst1836_0 in
lemma booleanMonomial_mul [Fintype α] (S T : Finset α) :
    booleanMonomial (𝕜 := 𝕜) S * booleanMonomial T = booleanMonomial (S ∪ T) := by
  ext B
  simp only [booleanMonomial, Pi.mul_apply, Finset.union_subset_iff]
  split_ifs <;> simp_all

omit inst1836_0 in
lemma booleanMonomial_mem [Fintype α] {S : Finset α} {d : ℕ} (h : S.card ≤ d) :
    booleanMonomial (𝕜 := 𝕜) S ∈ booleanDegreeSpace d :=
  Submodule.subset_span ⟨⟨S,h⟩, rfl⟩

lemma boolean_one_mem (d : ℕ) : (1 : Finset α → 𝕜) ∈ booleanDegreeSpace d := by
  convert booleanMonomial_mem (α := α) (𝕜 := 𝕜) (S := ∅) (Nat.zero_le d) using 1
  ext B
  simp [booleanMonomial]

lemma boolean_mul_mem {d e : ℕ} {f g : Finset α → 𝕜}
    (hf : f ∈ booleanDegreeSpace d) (hg : g ∈ booleanDegreeSpace e) :
    f*g ∈ booleanDegreeSpace (d+e) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨⟨S,hS⟩,rfl⟩ := hf
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨⟨T,hT⟩,rfl⟩ := hg
      rw [booleanMonomial_mul]
      exact booleanMonomial_mem ((Finset.card_union_le S T).trans (Nat.add_le_add hS hT))
    | zero => simp
    | add g h _ _ hg hh => simpa only [mul_add] using Submodule.add_mem _ hg hh
    | smul c g _ hg => simpa only [mul_smul_comm] using Submodule.smul_mem _ c hg
  | zero => simp
  | add f h _ _ hf hh => simpa only [add_mul] using Submodule.add_mem _ hf hh
  | smul c f _ hf => simpa only [smul_mul_assoc] using Submodule.smul_mem _ c hf

lemma boolean_pow_mem {f : Finset α → 𝕜} (hf : f ∈ booleanDegreeSpace 1) (n : ℕ) :
    f^n ∈ booleanDegreeSpace n := by
  induction n with
  | zero => simpa using boolean_one_mem (α := α) (𝕜 := 𝕜) 0
  | succ n ih => simpa only [pow_succ] using boolean_mul_mem ih hf

def intersectionSum (A : Finset α) : Finset α → 𝕜 :=
  ∑ h ∈ A, booleanMonomial {h}

lemma intersectionSum_mem (A : Finset α) :
    intersectionSum (𝕜 := 𝕜) A ∈ booleanDegreeSpace 1 := by
  apply Submodule.sum_mem
  intro h hh
  exact booleanMonomial_mem (by simp)

omit inst1836_0 in
lemma intersectionSum_apply [Fintype α] (A B : Finset α) :
    intersectionSum (𝕜 := 𝕜) A B = (A ∩ B).card := by
  simp only [intersectionSum, Finset.sum_apply, booleanMonomial, Finset.singleton_subset_iff]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  congr 1

universe v1900_0

lemma boolean_biorthogonal_bound {ν : Type v1900_0} [Fintype ν] [DecidableEq ν]
    (f : ν → Finset α → 𝕜) (eval : ν → Finset α)
    (d : ℕ) (hmem : ∀ v, f v ∈ booleanDegreeSpace d)
    (heval : ∀ v w, f v (eval w) = if v=w then 1 else 0) :
    Fintype.card ν ≤ Fintype.card {S : Finset α // S.card ≤ d} := by
  classical
  have hlin : LinearIndependent 𝕜 f := by
    rw [linearIndependent_iff']
    intro S c hc v hv
    have h := congrFun hc (eval v)
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      heval, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', ite_eq_left hv] using h
  rw [← finrank_span_eq_card hlin]
  exact (Submodule.finrank_mono (Submodule.span_le.mpr (by
    rintro _ ⟨v,rfl⟩
    exact hmem v))).trans (finrank_range_le_card _)

omit inst1836_1 in
lemma card_booleanMonomials [DecidableEq α] (d : ℕ) :
    Fintype.card {S : Finset α // S.card ≤ d} =
      ∑ j ∈ Finset.range (d+1), Nat.choose (Fintype.card α) j := by
  let e : {S : Finset α // S.card ≤ d} ≃
      (Σ j : Fin (d+1), {S : Finset α // S.card = j.val}) :=
    { toFun := fun S => ⟨⟨S.1.card, Nat.lt_succ_of_le S.2⟩, ⟨S.1,rfl⟩⟩
      invFun := fun S => ⟨S.2.1, by rw [S.2.2]; exact Nat.le_of_lt_succ S.1.2⟩
      left_inv := fun _ => rfl
      right_inv := by rintro ⟨⟨j,hj⟩,S,hS⟩; cases hS; rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  have hc (j : ℕ) : Fintype.card {S : Finset α // S.card=j} = Nat.choose (Fintype.card α) j := by
    rw [Fintype.card_of_subtype ((Finset.univ : Finset α).powersetCard j) (by
      intro S
      simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and])]
    rw [Finset.card_powersetCard, Finset.card_univ]
  simp only [hc]
  exact Fin.sum_univ_eq_sum_range _ _

end BooleanFunctions

universe v1938_0

lemma modular_intersection_bound {α : Type v1938_0} [Fintype α] [DecidableEq α]
    (p : ℕ) [Fact p.Prime] (F : Finset (Finset α))
    (hself : ∀ A ∈ F, ((A.card : ℕ) : ZMod p) = 0)
    (hdist : ∀ A ∈ F, ∀ B ∈ F, A ≠ B → (((A ∩ B).card : ℕ) : ZMod p) ≠ 0) :
    F.card ≤ ∑ j ∈ Finset.range p, Nat.choose (Fintype.card α) j := by
  classical
  let f : F → Finset α → ZMod p := fun A => 1 - (intersectionSum A.1)^(p-1)
  have hmem (A : F) : f A ∈ booleanDegreeSpace (p-1) :=
    Submodule.sub_mem _ (boolean_one_mem _) (boolean_pow_mem (intersectionSum_mem A.1) _)
  have heval (A B : F) : f A B.1 = if A=B then 1 else 0 := by
    dsimp [f]
    simp only [intersectionSum_apply]
    by_cases h : A=B
    · subst B
      rw [ite_eq_left rfl, Finset.inter_self, hself A.1 A.2, zero_pow (by
        have hp := (Fact.out : p.Prime).two_le
        omega), sub_zero]
    · rw [ite_eq_right h, ZMod.pow_card_sub_one_eq_one (hdist A.1 A.2 B.1 B.2 (by
        exact fun he => h (Subtype.ext he))), sub_self]
  have hb := boolean_biorthogonal_bound f Subtype.val (p-1) hmem heval
  rw [Fintype.card_coe, card_booleanMonomials] at hb
  have hp := (Fact.out : p.Prime).two_le
  simpa only [Nat.sub_add_cancel (by omega : 1 ≤ p)] using hb

end

namespace Explicit

lemma overlap_product (q r : Question) :
    overlap q r = ∏ l, (((ofLex q l).1 ∩ (ofLex r l).1).card / (p:ℝ) - 1) := by
  change Lex (Fin 3 → Base) at q r
  unfold overlap vector
  simp only [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun l h => baseVector (ofLex q l) h * baseVector (ofLex r l) h)]
  simp only [base_inner]

lemma base_no_orthogonal_bound (F : Finset Base)
    (hF : ∀ A ∈ F, ∀ B ∈ F, A ≠ B → ∑ h, baseVector A h * baseVector B h ≠ 0) :
    F.card ≤ a₀ := by
  let : Fact (Nat.Prime p) := ⟨by norm_num [p]⟩
  let G : Finset (Finset (Fin k)) := F.image Subtype.val
  have hG := ZeroKey.modular_intersection_bound p G
  have hs : ∀ A ∈ G, (A.card : ZMod p) = 0 := by
    intro A hA
    obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp hA
    rw [B.2.1, ZMod.natCast_eq_zero_iff]
    norm_num [p]
  have hd : ∀ A ∈ G, ∀ B ∈ G, A ≠ B → ((A ∩ B).card : ZMod p) ≠ 0 := by
    intro A hA B hB hne hz
    obtain ⟨A',hA',rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨B',hB',rfl⟩ := Finset.mem_image.mp hB
    change Base at A' B'
    have hn : A' ≠ B' := fun h => hne (congrArg Subtype.val h)
    have hp : 0 < (A'.1 ∩ B'.1).card := Finset.card_pos.mpr
      ⟨0, Finset.mem_inter.mpr ⟨A'.2.2, B'.2.2⟩⟩
    have hl : (A'.1 ∩ B'.1).card < 514 := by
      have hle := Finset.card_le_card (Finset.inter_subset_left : A'.1 ∩ B'.1 ⊆ A'.1)
      rw [A'.2.1] at hle
      apply lt_of_le_of_ne hle
      intro he
      have hab : A'.1 ⊆ B'.1 := by
        have heq : A'.1 ∩ B'.1 = A'.1 := Finset.eq_of_subset_of_card_le
          Finset.inter_subset_left (by rw [he, A'.2.1])
        exact Finset.inter_eq_left.mp heq
      exact hne (Finset.eq_of_subset_of_card_le hab (by rw [A'.2.1,B'.2.1]))
    obtain ⟨j,hj⟩ := (ZMod.natCast_eq_zero_iff _ _).mp hz
    have hi : (A'.1 ∩ B'.1).card = 257 := by dsimp [p] at hj; omega
    have ho := hF A' hA' B' hB' hn
    rw [base_inner, hi] at ho
    norm_num [p] at ho
  have h := hG hs hd
  have hc : G.card = F.card := Finset.card_image_of_injective _ Subtype.val_injective
  rw [hc, Fintype.card_fin] at h
  delta a₀
  exact h

end Explicit

universe v2084_0 v2084_1

def OrProduct {α : Type v2084_0} {β : Type v2084_1} (R : α → α → Prop) (S : β → β → Prop) :
    α × β → α × β → Prop := fun x y => R x.1 y.1 ∨ S x.2 y.2

universe v2087_0 v2087_1

lemma two_fibers_clique {α : Type v2087_0} {β : Type v2087_1} [DecidableEq α] [DecidableEq β]
    (R : α → α → Prop) (S : β → β → Prop) (hR : (∀ ⦃left right⦄, R left right → R right left))
    {a a' : α} (_haa : a ≠ a') (har : R a a')
    (T T' : Finset β) (hT : (T : Set β).Pairwise S) (hT' : (T' : Set β).Pairwise S) :
    ((T.image (fun b => (a,b)) ∪ T'.image (fun b => (a',b)) : Finset (α × β)) : Set (α × β)).Pairwise (OrProduct R S) := by
  intro x hx y hy hxy
  rcases Finset.mem_union.mp hx with hx | hx <;>
    rcases Finset.mem_union.mp hy with hy | hy
  · obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hy
    exact Or.inr (hT hb hc (fun h => hxy (by rw [h])))
  · obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hy
    exact Or.inl har
  · obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hy
    exact Or.inl (hR har)
  · obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hy
    exact Or.inr (hT' hb hc (fun h => hxy (by rw [h])))

universe v2109_0 v2109_1

lemma rich_fiber_bound {α : Type v2109_0} {β : Type v2109_1} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (R : α → α → Prop) (S : β → β → Prop) (hR : (∀ ⦃left right⦄, R left right → R right left))
    (a b r : ℕ)
    (hA : ∀ F : Finset α, (∀ x ∈ F, ∀ y ∈ F, x ≠ y → ¬R x y) → F.card ≤ a)
    (hB : ∀ F : Finset β, (¬∃ T ⊆ F, T.card=r ∧ (T : Set β).Pairwise S) → F.card ≤ b)
    (F : Finset (α × β))
    (hF : ¬∃ T ⊆ F, T.card=2*r ∧ (T : Set (α × β)).Pairwise (OrProduct R S)) :
    F.card ≤ a * Fintype.card β + b * Fintype.card α := by
  classical
  let fiber (x : α) : Finset β := Finset.univ.filter (fun y => (x,y) ∈ F)
  let rich : Finset α := Finset.univ.filter (fun x => ∃ T ⊆ fiber x, T.card=r ∧ (T : Set β).Pairwise S)
  have hrich : rich.card ≤ a := by
    apply hA
    intro x hx y hy hxy hrel
    obtain ⟨T,hT,hTc,hTp⟩ := (Finset.mem_filter.mp hx).2
    obtain ⟨T',hT',hTc',hTp'⟩ := (Finset.mem_filter.mp hy).2
    let U := T.image (fun z => (x,z)) ∪ T'.image (fun z => (y,z))
    apply hF
    refine ⟨U, ?_, ?_, two_fibers_clique R S hR hxy hrel T T' hTp hTp'⟩
    · intro z hz
      rcases Finset.mem_union.mp hz with hz | hz
      · obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
        exact (Finset.mem_filter.mp (hT hw)).2
      · obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
        exact (Finset.mem_filter.mp (hT' hw)).2
    · have hd : Disjoint (T.image (fun z => (x,z))) (T'.image (fun z => (y,z))) := by
        rw [Finset.disjoint_left]
        intro z hz hz'
        obtain ⟨u,hu,heu⟩ := Finset.mem_image.mp hz
        obtain ⟨v,hv,hev⟩ := Finset.mem_image.mp hz'
        exact hxy (congrArg Prod.fst (heu.trans hev.symm))
      dsimp [U]
      rw [Finset.card_union_of_disjoint hd,
        Finset.card_image_of_injective _ (fun _ _ h => Prod.mk.inj h |>.2),
        Finset.card_image_of_injective _ (fun _ _ h => Prod.mk.inj h |>.2), hTc,hTc']
      omega
  have cf (x : α) : (F.filter (fun z => z.1=x)).card = (fiber x).card := by
    apply Finset.card_bij (fun z _ => z.2)
    · intro z hz
      obtain ⟨hz,he⟩ := Finset.mem_filter.mp hz
      apply Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      simpa only [← he, Prod.eta] using hz
    · intro z hz w hw he
      apply Prod.ext
      · exact (Finset.mem_filter.mp hz).2.trans (Finset.mem_filter.mp hw).2.symm
      · exact he
    · intro z hz
      exact ⟨(x,z), Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).2,rfl⟩,rfl⟩
  have hc : F.card = ∑ x, (fiber x).card := by
    rw [Finset.card_eq_sum_card_fiberwise (t := Finset.univ) (f := Prod.fst)
      (fun _ _ => Finset.mem_univ _)]
    simp only [cf]
  have hbound (x : α) : (fiber x).card ≤ (if x ∈ rich then Fintype.card β else 0)+b := by
    by_cases hx : x ∈ rich
    · rw [ite_eq_left hx]
      exact (Finset.card_le_univ _).trans (Nat.le_add_right _ _)
    · rw [ite_eq_right hx, Nat.zero_add]
      apply hB
      simpa only [rich, Finset.mem_filter, Finset.mem_univ, true_and] using hx
  calc
    F.card = ∑ x, (fiber x).card := hc
    _ ≤ ∑ x, ((if x ∈ rich then Fintype.card β else 0)+b) := Finset.sum_le_sum (fun x _ => hbound x)
    _ = rich.card * Fintype.card β + b * Fintype.card α := by
      rw [Finset.sum_add_distrib]
      simp [Nat.mul_comm]
    _ ≤ a * Fintype.card β + b * Fintype.card α := Nat.add_le_add_right (Nat.mul_le_mul_right _ hrich) _

namespace Explicit

section

def BaseOrthogonal (A B : Base) : Prop := ∑ h, baseVector A h * baseVector B h = 0

lemma base_orthogonal_symm : (∀ ⦃left right⦄, BaseOrthogonal left right → BaseOrthogonal right left) := by
  intro A B h
  simpa only [BaseOrthogonal, mul_comm] using h

lemma base_no_two_bound (F : Finset Base)
    (hF : ¬∃ T ⊆ F, T.card=2 ∧ (T : Set Base).Pairwise BaseOrthogonal) : F.card ≤ a₀ := by
  apply base_no_orthogonal_bound F
  intro A hA B hB hne horth
  apply hF
  refine ⟨{A,B}, ?_, by simp [hne], ?_⟩
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hA
    · exact hB
  intro x hx y hy hxy
  simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact (hxy rfl).elim
  · exact horth
  · exact base_orthogonal_symm horth
  · exact (hxy rfl).elim

lemma pair_no_four_bound (F : Finset (Base × Base))
    (hF : ¬∃ T ⊆ F, T.card=4 ∧ (T : Set (Base × Base)).Pairwise
      (OrProduct BaseOrthogonal BaseOrthogonal)) : F.card ≤ 2*a₀*b := by
  have h := rich_fiber_bound BaseOrthogonal BaseOrthogonal base_orthogonal_symm a₀ a₀ 2
    base_no_orthogonal_bound base_no_two_bound F hF
  rw [card_base] at h
  calc F.card ≤ a₀*b+a₀*b := h
       _ = 2*a₀*b := by ring

lemma triple_no_eight_bound (F : Finset (Base × (Base × Base)))
    (hF : ¬∃ T ⊆ F, T.card=8 ∧ (T : Set (Base × (Base × Base))).Pairwise
      (OrProduct BaseOrthogonal (OrProduct BaseOrthogonal BaseOrthogonal))) :
    F.card ≤ 3*a₀*b^2 := by
  have h := rich_fiber_bound BaseOrthogonal (OrProduct BaseOrthogonal BaseOrthogonal)
    base_orthogonal_symm a₀ (2*a₀*b) 4 base_no_orthogonal_bound pair_no_four_bound F hF
  rw [Fintype.card_prod, card_base] at h
  calc F.card ≤ a₀*(b*b)+(2*a₀*b)*b := h
       _ = 3*a₀*b^2 := by ring

def questionTriple : Question ≃ Base × (Base × Base) where
  toFun q := (ofLex q 0, (ofLex q 1, ofLex q 2))
  invFun t := toLex ![t.1,t.2.1,t.2.2]
  left_inv q := by
    change toLex ![ofLex q 0,ofLex q 1,ofLex q 2] = q
    apply ofLex.injective
    ext i
    fin_cases i <;> rfl
  right_inv t := rfl

lemma questionTriple_apply (q : Question) :
    questionTriple q = (ofLex q 0, (ofLex q 1, ofLex q 2)) := rfl

lemma overlap_zero_iff (q r : Question) : overlap q r = 0 ↔
    OrProduct BaseOrthogonal (OrProduct BaseOrthogonal BaseOrthogonal)
      (questionTriple q) (questionTriple r) := by
  rw [overlap_product]
  rw [questionTriple_apply, questionTriple_apply]
  change _ ↔ BaseOrthogonal (ofLex q 0) (ofLex r 0) ∨
    BaseOrthogonal (ofLex q 1) (ofLex r 1) ∨ BaseOrthogonal (ofLex q 2) (ofLex r 2)
  simp only [Fin.prod_univ_three, mul_eq_zero, BaseOrthogonal, base_inner, or_assoc]

universe v2247_0 v2247_1

lemma no_clique_image {α : Type v2247_0} {β : Type v2247_1} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (R : α → α → Prop) (S : β → β → Prop)
    (hRS : ∀ x y, R x y ↔ S (e x) (e y)) (n : ℕ) (F : Finset α)
    (hF : ¬∃ T ⊆ F, T.card=n ∧ (T : Set α).Pairwise R) :
    ¬∃ T ⊆ F.map e.toEmbedding, T.card=n ∧ (T : Set β).Pairwise S := by
  rintro ⟨T,hT,hc,hp⟩
  apply hF
  refine ⟨T.map e.symm.toEmbedding, ?_, by simpa using hc, ?_⟩
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨z,hz,he⟩ := Finset.mem_map.mp (hT hy)
    simpa only [← he, Equiv.toEmbedding_apply, Equiv.symm_apply_apply] using hz
  · intro x hx y hy hxy
    obtain ⟨u,hu,rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨v,hv,rfl⟩ := Finset.mem_map.mp hy
    apply (hRS _ _).mpr
    simpa only [Equiv.toEmbedding_apply, Equiv.apply_symm_apply] using
      hp hu hv (fun he => hxy (congrArg e.symm he))

theorem vector_family_bound (F : Finset Question)
    (hF : ¬∃ T ⊆ F, T.card=8 ∧ (T : Set Question).Pairwise (fun q r => overlap q r=0)) :
    F.card ≤ 3*a₀*b^2 := by
  have h := triple_no_eight_bound (F.map questionTriple.toEmbedding)
    (no_clique_image questionTriple _ _ overlap_zero_iff 8 F hF)
  simpa only [Finset.card_map] using h

open Finset

lemma vector_family_strict : (3*a₀*b^2)*K < Q := by
  have h := Nat.mul_lt_mul_of_pos_right strict_parameter_bound (pow_pos b_pos 2)
  delta Q
  calc
    (3*a₀*b^2)*K = (3*a₀*K)*b^2 := by ring
    _ < b*b^2 := h
    _ = b^3 := by ring

end

lemma projection_orthogonal_of_question_eq {i j : Label}
    (hq : (ofLex i).1 = (ofLex j).1) (hij : i≠j) : projection i * projection j = 0 := by
  let e : Label ≃ Question × OutcomeString := Equiv.refl _
  have ha : (ofLex i).2 ≠ (ofLex j).2 := fun hh => hij (e.injective (Prod.ext hq hh))
  have hi : (toLex ((ofLex i).1, (ofLex i).2) : Label) = i := rfl
  have hj : (toLex ((ofLex i).1, (ofLex j).2) : Label) = j := e.injective (Prod.ext hq rfl)
  have hh := projection_orthogonal (ofLex i).1 (ofLex i).2 (ofLex j).2 ha
  rw [hi,hj] at hh
  exact hh

lemma localProjection_ordered (S : EightSet) (hS : PairwiseOrthogonal S) (t : Fin 6) :
    localProjection S ((S.1.orderIsoOfFin S.2) (Fin.castLE (by decide : 6≤8) t)).1 =
      contextProjection t := by
  change {S : Finset Question // S.card=8} at S
  funext a
  unfold localProjection
  rw [ite_eq_left hS, dite_eq_left ((S.1.orderIsoOfFin S.2) (Fin.castLE (by decide) t)).2]
  simp only [Subtype.coe_eta, OrderIso.symm_apply_apply, Fin.val_castLE]
  rw [dite_eq_left t.isLt]

lemma clique_no_eight (J : Finset Label)
    (hJ : ∀ i ∈ J, ∀ j ∈ J, i≠j → 0 < (trace (projection i * projection j)).re) :
    ¬∃ T ⊆ J.image (fun i => (ofLex i).1), T.card=8 ∧
      (T : Set Question).Pairwise (fun q r => overlap q r=0) := by
  rintro ⟨T,hTJ,hT,horth⟩
  let S : EightSet := ⟨T,hT⟩
  have hS : PairwiseOrthogonal S := fun q hq r hr hqr => horth hq hr hqr
  let q (t : Fin 6) : Question := ((T.orderIsoOfFin hT) (Fin.castLE (by decide : 6≤8) t)).1
  have hq (t : Fin 6) : q t ∈ T := ((T.orderIsoOfFin hT) (Fin.castLE (by decide) t)).2
  have hpick (t : Fin 6) : ∃ i ∈ J, (ofLex i).1 = q t := Finset.mem_image.mp (hTJ (hq t))
  choose i hi he using hpick
  let a (t : Fin 6) : Outcome := ofLex (ofLex (i t)).2 S
  apply magic_parity a
  intro t s hts
  have hqq : q t ≠ q s := by
    intro hh
    have hh' := (T.orderIsoOfFin hT).injective (Subtype.ext hh)
    exact hts (Fin.ext (congrArg (fun u : Fin 8 => u.val) hh'))
  have hii : i t ≠ i s := fun hh => hqq (by rw [← he t, ← he s, hh])
  have hh := local_trace_pos_of_global (i t) (i s) (hJ _ (hi t) _ (hi s) hii) S
  rw [he t, he s] at hh
  have ht := localProjection_ordered S hS t
  have hs := localProjection_ordered S hS s
  change localProjection S (q t) = contextProjection t at ht
  change localProjection S (q s) = contextProjection s at hs
  rw [ht,hs] at hh
  exact hh

theorem projection_clique_bound (J : Finset Label)
    (hJ : ∀ i ∈ J, ∀ j ∈ J, i≠j → 0 < (trace (projection i * projection j)).re) :
    J.card ≤ 3*a₀*b^2 := by
  have hinj : Set.InjOn (fun i : Label => (ofLex i).1) (J : Set Label) := by
    intro i hi j hj he
    by_contra hij
    have hh := hJ i hi j hj hij
    rw [projection_orthogonal_of_question_eq he hij, trace_zero] at hh
    exact lt_irrefl 0 hh
  have hc := vector_family_bound (J.image (fun i => (ofLex i).1)) (clique_no_eight J hJ)
  rwa [Finset.card_image_of_injOn hinj] at hc

lemma rawOutput_compression (i j : Label) :
    rawOutput (i,i) (j,j) = (overlap (ofLex i).1 (ofLex j).1 : ℂ)^2 *
      trace (projection i * projection j) := by
  rw [rawOutput_trace]
  by_cases h : overlap (ofLex i).1 (ofLex j).1 = 0
  · simp only [block, h, Complex.ofReal_zero, zero_smul, zero_mul, trace_zero, zero_pow (by decide : 2≠0)]
  · have hp : (projection i * projection j) * (projection i * projection j) =
        projection i * projection j := by
      calc
        _ = projection i * (projection j * projection i) * projection j := by noncomm_ring
        _ = (projection i * projection i) * (projection j * projection j) := by
          rw [← (projection_commute i j h).eq]
          noncomm_ring
        _ = _ := by rw [(projection_projection i).isIdempotentElem,
          (projection_projection j).isIdempotentElem]
    rw [block, smul_mul_smul_comm, hp, trace_smul, pow_two]
    rfl

lemma projection_idem (i : Label) : projection i * projection i = projection i :=
  (projection_projection i).isIdempotentElem

lemma rawOutput_compression_trace : (∑ i, rawOutput (i,i) (i,i)) = (Q*D : ℕ) := by
  simp_rw [rawOutput_crossed_diagonal, projection_idem]
  rw [sum_label]
  have h (q : Question) : ∑ a : OutcomeString, trace (projection (makeLabel q a)) = (D:ℂ) := by
    simpa only [trace_sum, trace_one, card_basis] using congrArg Matrix.trace (projection_sum_makeLabel q)
  simp only [h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_question, Nat.cast_mul]

lemma rawOutput_compression_total : (∑ i, ∑ j, rawOutput (i,i) (j,j)) =
    (D:ℂ) * ∑ q, ∑ r, (overlap q r : ℂ)^2 := by
  simp_rw [rawOutput_compression, sum_label]
  change (∑ q, ∑ a : OutcomeString, ∑ r, ∑ b : OutcomeString,
    (overlap q r : ℂ)^2 * trace (projection (makeLabel q a) * projection (makeLabel r b))) = _
  conv_lhs =>
    arg 2; ext q
    rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, sum_projection_pair_trace]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun r _ => mul_comm _ _)

end Explicit

end ZeroKey

open scoped MatrixOrder ComplexOrder Kronecker

open Matrix

namespace ZeroKey

universe u

universe v2609_0

def sepOuter {ι : Type v2609_0} (u v : ι → ℂ) : Matrix ι ι ℂ :=
  fun i j => u i * star (v j)

variable {ι : Type u} [inst2613_0 : Fintype ι] [inst2613_1 : DecidableEq ι]

omit inst2613_1 in
lemma normSq_sum_le_support [DecidableEq ι] (z : ι → ℂ) :
    Complex.normSq (∑ i, z i) ≤
      ((Finset.univ.filter (fun i => z i ≠ 0)).card : ℝ) * ∑ i, Complex.normSq (z i) := by
  classical
  let S := Finset.univ.filter (fun i => z i ≠ 0)
  have hs : ∑ i, z i = ∑ i ∈ S, z i := by
    symm
    exact Finset.sum_filter_ne_zero _
  have hn : ∑ i, Complex.normSq (z i) = ∑ i ∈ S, Complex.normSq (z i) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i hi hnot
    have hz : z i = 0 := by simpa [S] using hnot
    simp [hz]
  rw [hs, hn, Complex.normSq_eq_norm_sq]
  have ht := norm_sum_le S z
  have hc := Finset.sum_mul_sq_le_sq_mul_sq S (fun i => ‖z i‖) (fun _ => (1:ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one,
    ← Complex.normSq_eq_norm_sq] at hc
  exact (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun _ _ => norm_nonneg _))).2 ht |>.trans
    (by simpa only [mul_comm] using hc)

universe v2637_0

lemma pure_decomposition_certificate {ν : Type v2637_0} [Fintype ν] (x y : ν → ι → ℂ)
    (G : Matrix (ι × ι) (ι × ι) ℂ)
    (hG : G = ∑ s, sepOuter (fun i => x s i.1 * y s i.2) (fun i => x s i.1 * y s i.2))
    (κ : ℕ)
    (hclique : ∀ S : Finset ι,
      (∀ i ∈ S, ∀ j ∈ S, i ≠ j → 0 < (G (i,j) (i,j)).re) → S.card ≤ κ) :
    (∑ i, ∑ j, G (i,i) (j,j)).re ≤ (κ:ℝ) * ∑ i, (G (i,i) (i,i)).re := by
  classical
  let z : ν → ι → ℂ := fun s i => x s i * y s i
  have hdiag (i j : ι) : (G (i,j) (i,j)).re =
      ∑ s, Complex.normSq (x s i * y s j) := by
    rw [hG]
    simp only [Matrix.sum_apply, sepOuter, Complex.star_def, Complex.mul_conj, Complex.re_sum, Complex.ofReal_re]
  have hzcard (s : ν) : (Finset.univ.filter (fun i => z s i ≠ 0)).card ≤ κ := by
    apply hclique
    intro i hi j hj _
    have hi' : x s i * y s i ≠ 0 := (Finset.mem_filter.mp hi).2
    have hj' : x s j * y s j ≠ 0 := (Finset.mem_filter.mp hj).2
    have hij : x s i * y s j ≠ 0 := mul_ne_zero (mul_ne_zero_iff.mp hi').1 (mul_ne_zero_iff.mp hj').2
    rw [hdiag]
    exact (Complex.normSq_pos.mpr hij).trans_le
      (Finset.single_le_sum (fun t _ => Complex.normSq_nonneg (x t i * y t j)) (Finset.mem_univ s))
  have hsum : (∑ i, ∑ j, G (i,i) (j,j)).re = ∑ s, Complex.normSq (∑ i, z s i) := by
    have hc : (∑ i, ∑ j, G (i,i) (j,j)) =
        ∑ s, (Complex.normSq (∑ i, z s i) : ℂ) := by
      rw [hG]
      simp only [Matrix.sum_apply, sepOuter, Complex.normSq_eq_conj_mul_self,
        map_sum, Finset.sum_mul, Finset.mul_sum, z, starRingEnd_apply]
      conv_lhs => rw [Finset.sum_comm]; arg 2; ext j; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hc, Complex.re_sum]
    simp only [Complex.ofReal_re]
  rw [hsum]
  calc
    _ ≤ ∑ s, (κ:ℝ) * ∑ i, Complex.normSq (z s i) := by
      apply Finset.sum_le_sum
      intro s _
      exact (normSq_sum_le_support (z s)).trans
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hzcard s)
          (Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _)))
    _ = _ := by
      simp only [← Finset.mul_sum, z, hdiag]
      rw [Finset.sum_comm]

lemma sqrt_column_decomposition (A : Matrix ι ι ℂ) (hA : A.PosSemidef) (i j : ι) :
    A i j = ∑ k, (CFC.sqrt A) i k * star ((CFC.sqrt A) j k) := by
  have h : A = CFC.sqrt A * (CFC.sqrt A)ᴴ := by
    rw [(CFC.sqrt_nonneg A).posSemidef.isHermitian.eq]
    exact (CFC.sqrt_mul_sqrt_self A hA.nonneg).symm
  conv_lhs => rw [h]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]

lemma separable_has_pure_decomposition (G : Matrix (ι × ι) (ι × ι) ℂ)
    (hG : Separable G) :
    ∃ (ν : Type u) (_ : Fintype ν) (x y : ν → ι → ℂ),
      G = ∑ s, sepOuter (fun i => x s i.1 * y s i.2) (fun i => x s i.1 * y s i.2) := by
  classical
  obtain ⟨n,A,B,hA,hB,hG⟩ := hG
  refine ⟨Fin n × (ι × ι), inferInstance,
    (fun s i => CFC.sqrt (A s.1) i s.2.1),
    (fun s i => CFC.sqrt (B s.1) i s.2.2), ?_⟩
  rw [hG]
  ext ⟨i,j⟩ ⟨k,l⟩
  simp only [Matrix.sum_apply, Matrix.kronecker_apply, Fintype.sum_prod_type, sepOuter]
  apply Finset.sum_congr rfl
  intro s _
  rw [sqrt_column_decomposition _ (hA s) i k, sqrt_column_decomposition _ (hB s) j l]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp only [star_mul]
  ring

theorem separable_support_certificate
    (G : Matrix (ι × ι) (ι × ι) ℂ) (hG : Separable G) (κ : ℕ)
    (hclique : ∀ S : Finset ι,
      (∀ i ∈ S, ∀ j ∈ S, i ≠ j → 0 < (G (i,j) (i,j)).re) → S.card ≤ κ) :
    (∑ i, ∑ j, G (i,i) (j,j)).re ≤ (κ:ℝ) * ∑ i, (G (i,i) (i,i)).re := by
  obtain ⟨ν,hν,x,y,h⟩ := separable_has_pure_decomposition G hG
  let := hν
  exact pure_decomposition_certificate x y G h κ hclique

theorem not_separable_of_support_certificate
    (G : Matrix (ι × ι) (ι × ι) ℂ) (κ : ℕ)
    (hclique : ∀ S : Finset ι,
      (∀ i ∈ S, ∀ j ∈ S, i ≠ j → 0 < (G (i,j) (i,j)).re) → S.card ≤ κ)
    (hgap : (κ:ℝ) * ∑ i, (G (i,i) (i,i)).re < (∑ i, ∑ j, G (i,i) (j,j)).re) :
    ¬ Separable G := by
  intro h
  exact (not_le_of_gt hgap) (separable_support_certificate G h κ hclique)

end ZeroKey

open Finset

namespace ZeroKey

section

universe v2749_0 v2749_1

variable {α : Type v2749_0} {β : Type v2749_1} [inst2749_0 : Fintype α] [inst2749_1 : Fintype β]

lemma frame_potential_rearrange (u : α → β → ℝ) :
    (∑ q, ∑ r, (∑ h, u q h * u r h)^2) =
      ∑ h, ∑ l, (∑ q, u q h * u q l)^2 := by
  simp only [pow_two, sum_mul, mul_sum]
  conv_lhs =>
    arg 2; ext q
    rw [sum_comm]
  rw [sum_comm]
  conv_lhs =>
    arg 2; ext h
    arg 2; ext q
    rw [sum_comm]
  conv_lhs =>
    arg 2; ext h
    rw [sum_comm]
  apply sum_congr rfl
  intro h _
  apply sum_congr rfl
  intro l _
  apply sum_congr rfl
  intro q _
  apply sum_congr rfl
  intro r _
  ring

theorem frame_potential_bound (u : α → β → ℝ) (hu : ∀ q, ∑ h, u q h * u q h = 1) :
    (Fintype.card α : ℝ)^2 ≤ (Fintype.card β : ℝ) *
      ∑ q, ∑ r, (∑ h, u q h * u r h)^2 := by
  classical
  have ht : ∑ h, ∑ q, u q h * u q h = (Fintype.card α : ℝ) := by
    rw [sum_comm]
    simp only [hu, sum_const, card_univ, nsmul_eq_mul, mul_one]
  have hc := sum_mul_sq_le_sq_mul_sq univ (fun h => ∑ q, u q h * u q h) (fun _ => (1:ℝ))
  simp only [mul_one, ht, one_pow, sum_const, card_univ, nsmul_eq_mul] at hc
  have hd : (∑ h, (∑ q, u q h * u q h)^2) ≤ ∑ h, ∑ l, (∑ q, u q h * u q l)^2 := by
    apply sum_le_sum
    intro h _
    exact single_le_sum (fun l _ => sq_nonneg (∑ q, u q h * u q l)) (mem_univ h)
  rw [frame_potential_rearrange]
  calc
    (Fintype.card α : ℝ)^2 ≤ (Fintype.card β : ℝ) * ∑ h, (∑ q, u q h * u q h)^2 := by
      simpa only [mul_comm] using hc
    _ ≤ _ := mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg _)

end

namespace Explicit

lemma K_pos : 0 < K := by unfold K; exact pow_pos (by decide) 3

lemma card_vectorIndex : Fintype.card (Fin 3 → Fin k) = K := by

  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  unfold K
  rfl

theorem rawOutput_not_separable : ¬ Separable rawOutput := by
  apply not_separable_of_support_certificate rawOutput (3*a₀*b^2)
  · intro J hJ
    exact projection_clique_bound J (by simpa only [rawOutput_crossed_diagonal] using hJ)
  · let S : ℝ := ∑ q, ∑ r, (overlap q r)^2
    have hfr : (Q:ℝ)^2 ≤ (K:ℝ)*S := by
      have hh := frame_potential_bound (α := Question) (β := Fin 3 → Fin k)
        vector (fun q => show (∑ h, vector q h * vector q h)=1 from vector_unit q)
      rw [card_question, card_vectorIndex] at hh
      exact hh
    have hst : ((3*a₀*b^2 : ℕ):ℝ)*(K:ℝ) < (Q:ℝ) := by
      exact_mod_cast vector_family_strict
    have hq : (0:ℝ)<Q := by exact_mod_cast Q_pos
    have hk : (0:ℝ)<K := by exact_mod_cast K_pos
    have hd : (0:ℝ)<D := by exact_mod_cast D_pos
    have hs : ((3*a₀*b^2 : ℕ):ℝ)*(Q:ℝ) < S := by nlinarith
    have ht : (∑ i, (rawOutput (i,i) (i,i)).re) = (Q:ℝ)*(D:ℝ) := by
      rw [← Complex.re_sum, rawOutput_compression_trace]
      simp only [Nat.cast_mul, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
        zero_mul, sub_zero]
    have hu : (∑ i, ∑ j, rawOutput (i,i) (j,j)).re = (D:ℝ)*S := by
      rw [rawOutput_compression_total]
      simp only [← Complex.ofReal_natCast, ← Complex.ofReal_pow, ← Complex.ofReal_sum,
        ← Complex.ofReal_mul, Complex.ofReal_re]
      rfl
    rw [ht, hu]
    nlinarith

end Explicit

end ZeroKey

open scoped ComplexOrder MatrixOrder Kronecker

open Matrix

namespace ZeroKey

section

namespace Explicit

lemma blockFin_transpose (i j : Fin m) : (blockFin i j)ᵀ = blockFin i j := by
  unfold blockFin
  exact congrArg (fun A : Matrix Basis Basis ℂ => A.submatrix basisOrder basisOrder)
    (block_transpose (labelOrder i) (labelOrder j))

lemma trace_transpose_left (A U : Mat D) : trace (A * Uᵀ) = trace (Aᵀ * U) := by
  simp only [trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]

lemma constructionMapFin_transpose : constructionMapFin.comp (transposeLinear D) = constructionMapFin := by
  ext U i j
  change trace (blockFin i j * Uᵀ) = trace (blockFin i j * U)
  rw [trace_transpose_left, blockFin_transpose]

lemma constructionMapFin_ppt : PPTType constructionMapFin := by
  exact ⟨constructionMapFin_cp, by rw [constructionMapFin_transpose]; exact constructionMapFin_cp⟩

end Explicit

universe v2984_0 v2984_1 v2984_2 v2984_3

variable {ι : Type v2984_0} {κ : Type v2984_1} {α : Type v2984_2} {β : Type v2984_3} [inst2984_0 : Fintype ι] [inst2984_1 : Fintype κ] [inst2984_2 : Fintype α] [inst2984_3 : Fintype β]

lemma Separable.smul {G : Matrix (ι × κ) (ι × κ) ℂ} (hG : Separable G)
    {c : ℂ} (hc : 0 ≤ c) : Separable (c • G) := by
  obtain ⟨n,A,B,hA,hB,rfl⟩ := hG
  refine ⟨n,fun s => c • A s,B,fun s => (hA s).smul hc,hB,?_⟩
  simp only [Finset.smul_sum, Matrix.smul_kronecker]

lemma Separable.submatrix {G : Matrix (ι × κ) (ι × κ) ℂ} (hG : Separable G)
    (f : α → ι) (g : β → κ) :
    Separable (G.submatrix (Prod.map f g) (Prod.map f g)) := by
  obtain ⟨n,A,B,hA,hB,rfl⟩ := hG
  refine ⟨n,fun s => (A s).submatrix f f,fun s => (B s).submatrix g g,
    fun s => (hA s).submatrix f,fun s => (hB s).submatrix g,?_⟩
  ext ⟨i,j⟩ ⟨k,l⟩
  simp only [Matrix.submatrix_apply, Matrix.sum_apply, Matrix.kronecker_apply, Prod.map_apply]

end

namespace Explicit

lemma rawOutputFin_not_separable : ¬ Separable rawOutputFin := by
  intro h
  apply rawOutput_not_separable
  have hh := h.submatrix labelOrder.symm labelOrder.symm
  convert hh using 1
  ext ⟨i,j⟩ ⟨k,l⟩
  simp only [rawOutputFin, Matrix.submatrix_apply, Prod.map_apply,
    OrderIso.apply_symm_apply]

lemma rhoFin_not_separable : ¬ Separable rhoFin := by
  intro h
  apply rawOutputFin_not_separable
  have hh := h.smul (Nat.cast_nonneg (α := ℂ) (Q^2*D))
  rw [rhoFin_eq, smul_smul, mul_inv_cancel₀ normalization_ne_zero, one_smul] at hh
  exact hh

lemma rhoFin_inClass : InClass rhoFin := by
  refine ⟨rhoFin_density, D,D,constructionMapFin,constructionMapFin,
    (fun i => ((Real.sqrt (Q^2*D : ℕ))⁻¹ : ℝ) * omegaVector i),
    constructionMapFin_ppt,constructionMapFin_ppt,?_⟩
  have hc : ((((Real.sqrt (Q^2*D : ℕ))⁻¹ : ℝ) : ℂ) *
      (((Real.sqrt (Q^2*D : ℕ))⁻¹ : ℝ) : ℂ)) = ((Q^2*D : ℕ) : ℂ)⁻¹ := by
    rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg _),
      Complex.ofReal_inv, Complex.ofReal_natCast]
  have ho : outer (fun i => ((Real.sqrt (Q^2*D : ℕ))⁻¹ : ℝ) * omegaVector i)
      (fun i => ((Real.sqrt (Q^2*D : ℕ))⁻¹ : ℝ) * omegaVector i) =
      ((Q^2*D : ℕ) : ℂ)⁻¹ • outer omegaVector omegaVector := by
    ext i j
    simp only [outer, star_mul, Complex.star_def, Complex.conj_ofReal,
      Matrix.smul_apply, smul_eq_mul]
    rw [← hc]
    ring
  rw [ho, tensorMap_smul, ← rawOutputFin_tensor, ← rhoFin_eq]

theorem explicit_entangled_class_state :
    Density rhoFin ∧ ¬ Separable rhoFin ∧ InClass rhoFin :=
  ⟨rhoFin_density,rhoFin_not_separable,rhoFin_inClass⟩

end Explicit

end ZeroKey

end

end OAI
