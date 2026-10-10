import Mathlib
import OAI.Probability.SKGap.Localization.ResidualRecipe2

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary
variable {n M : ℕ} {κ σ : Type*} [Fintype κ] [DecidableEq κ] [Fintype σ]
namespace OrdinaryData

def Admissible (D : OrdinaryData n (Fin M) κ σ) (N p : ℕ) : Prop :=
  ∀a≤N,∀q:Fin M,q.val<p→ (∀s,D.seedPartial a q s=0) ∧ (∀b,D.auxPartial a q b=0)

omit [Fintype σ] in
lemma Admissible.mono {D : OrdinaryData n (Fin M) κ σ} {N p r : ℕ}
    (h : D.Admissible N p) (hr : r≤p) : D.Admissible N r :=
  fun a ha q hq=>h a ha q (hq.trans_le hr)

omit [Fintype σ] in
lemma Admissible.prefix {D : OrdinaryData n (Fin M) κ σ} {N p A : ℕ}
    (h : D.Admissible N p) (hr : A≤N) : D.Admissible A p :=
  fun a ha=>h a (ha.trans hr)

lemma Admissible.sourcePartial {D : OrdinaryData n (Fin M) κ σ} {N p : ℕ}
    (h : D.Admissible N p) (a : ℕ) (ha : a≤N) (q : Fin M) (hq : q.val<p) :
    D.sourcePartial a q=0 := by
  ext x i
  simp only [OrdinaryData.sourcePartial,partialOf,(h a ha q hq).1,(h a ha q hq).2,
    Pi.zero_apply,zero_mul,Finset.sum_const_zero,add_zero]

omit [Fintype σ] in
lemma appendProduct_Admissible (D : OrdinaryData n (Fin M) κ σ) (N p : ℕ) (F F')
    (h : D.Admissible N p)
    (hf : ∀q:Fin M,q.val<p→ localPartial D.H D.θ F' (.inl q)=0) :
    (D.appendProduct N F F').Admissible (N+1) p := by
  intro a ha q hq
  by_cases he : a=N+1
  · subst a
    have hs:= (h N le_rfl q hq).1
    have hb:= (h N le_rfl q hq).2
    have hfs:=hf q hq
    constructor
    · intro s; ext x i
      have hs':partialAt (D.seedDerivative N s i (localArgs D.H D.θ x i)) (.inl q)=0 := congrFun (congrFun (hs s) x) i
      have hf':partialAt (F' i (localArgs D.H D.θ x i)) (.inl q)=0 := congrFun (congrFun hfs x) i
      simp [seedPartial,localPartial,appendProduct,partialAt] at hs' hf' ⊢
      rw [hs',hf']; ring
    · intro b; ext x i
      by_cases hh : b.val<N
      · have hb':partialAt (D.auxDerivative N ⟨b.val,hh⟩ i (localArgs D.H D.θ x i)) (.inl q)=0 :=
          congrFun (congrFun (hb ⟨b.val,hh⟩) x) i
        have hf':partialAt (F' i (localArgs D.H D.θ x i)) (.inl q)=0 := congrFun (congrFun hfs x) i
        simp [auxPartial,localPartial,appendProduct,partialAt,hh] at hb' hf' ⊢
        rw [hb',hf']; ring
      · simp [auxPartial,localPartial,appendProduct,hh,partialAt]
  · have haN : a≤N := by omega
    simpa only [seedPartial,auxPartial,localPartial,appendProduct,ite_eq_right he] using h a haN q hq

omit [Fintype σ] in
lemma appendStein_Admissible (D : OrdinaryData n (Fin M) κ σ) (N p : ℕ)
    (l m : Fin M) (α : κ) (hl : p≤l.val) (hm : p ≤ m.val)
    (h : D.Admissible N p) : (D.appendStein N l m α).Admissible (N+1) p := by
  apply D.appendProduct_Admissible N p _ _ h
  intro q hq
  ext x i
  exact phiDerivative_other l m q α (by intro he; subst q; omega) (by intro he; subst q; omega) i _

def appendAuxiliary (D : OrdinaryData n (Fin M) κ σ) (N : ℕ) : OrdinaryData n (Fin M) κ σ :=
  { D with
    seedFunction := fun a s i u=>if a=N+1 then 0 else D.seedFunction a s i u
    seedDerivative := fun a s i u=>if a=N+1 then 0 else D.seedDerivative a s i u
    auxFunction := fun a b i u=>if a=N+1 then if b.val=N then 1 else 0 else D.auxFunction a b i u
    auxDerivative := fun a b i u=>if a=N+1 then 0 else D.auxDerivative a b i u }

lemma appendAuxiliary_prefix (D : OrdinaryData n (Fin M) κ σ) (N : ℕ) :
    ∀a≤N,(D.appendAuxiliary N).source a=D.source a ∧
      (D.appendAuxiliary N).auxiliary a=D.auxiliary a := by
  apply evaluation_prefix_eq D (D.appendAuxiliary N) N rfl rfl rfl rfl
  all_goals
    intro a ha
    have hh : a≠N+1 := by omega
    simp [seedCoefficient,auxCoefficient,seedPartial,auxPartial,appendAuxiliary,hh]

lemma appendAuxiliary_source (D : OrdinaryData n (Fin M) κ σ) (N : ℕ) :
    (D.appendAuxiliary N).source (N+1)=D.auxiliary N := by
  rw [source_eq]
  ext x i
  dsimp only [sourceOf]
  rw [Fin.sum_univ_castSucc]
  have hy : (D.appendAuxiliary N).auxiliary N=D.auxiliary N := (D.appendAuxiliary_prefix N N le_rfl).2
  dsimp only [appendAuxiliary] at hy
  simp [seedCoefficient,auxCoefficient,coefficient,appendAuxiliary,hy,
    show ∀b:Fin N,b.val≠N from fun b=>Nat.ne_of_lt b.isLt]

omit [Fintype σ] in
lemma appendAuxiliary_Admissible (D : OrdinaryData n (Fin M) κ σ) (N p : ℕ)
    (h : D.Admissible N p) : (D.appendAuxiliary N).Admissible (N+1) p := by
  intro a ha q hq
  by_cases he : a=N+1
  · subst a
    constructor
    · intro s; ext x i; simp [seedPartial,localPartial,appendAuxiliary,partialAt]
    · intro b; ext x i; simp [auxPartial,localPartial,appendAuxiliary,partialAt]
  · have haN : a≤N := by omega
    simpa only [seedPartial,auxPartial,localPartial,appendAuxiliary,ite_eq_right he] using h a haN q hq

end OrdinaryData
end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
variable {n : ℕ} {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

namespace SegmentRegular
variable {H : ι→VectorFields n} {θ : κ→Spin n→ℝ}
variable {F G : Fin n→Args (ι:=ι) (κ:=κ)→ℝ}
variable {F' G' : Fin n→Args (ι:=ι) (κ:=κ)→Args (ι:=ι) (κ:=κ)→L[ℝ]ℝ}
variable {x : Spin n} {C D : ℝ}

omit [DecidableEq ι] [DecidableEq κ] in
lemma value_difference (h : SegmentRegular H θ F F' x C) (i k : Fin n)
    (t : ℝ) (ht : t∈Set.Icc (0:ℝ) 1) :
    |F i (localArgs H θ x i+t • (localArgs H θ (flip x k) i-localArgs H θ x i))-
      F i (localArgs H θ x i)|≤C*‖t • (localArgs H θ (flip x k) i-localArgs H θ x i)‖ := by
  let u:=localArgs H θ x i
  let v:=localArgs H θ (flip x k) i
  have hm (s : ℝ) (hs : s∈Set.Icc (0:ℝ) 1) : s*t∈Set.Icc (0:ℝ) 1 :=
    ⟨mul_nonneg hs.1 ht.1,(mul_le_mul hs.2 ht.2 ht.1 (by norm_num)).trans_eq (by norm_num)⟩
  have he (s : ℝ) : u+s • (u+t • (v-u)-u)=u+(s*t) • (v-u) := by module
  have hb:=SKGap.SourceTaylor.segment_lipschitz (F i) (F' i) u (u+t • (v-u)) h.nonneg
    (fun s hs=>by rw [he]; exact h.deriv i k (s*t) (hm s hs))
    (fun s hs=>by rw [he]; exact h.bound i k (s*t) (hm s hs))
  simpa only [add_sub_cancel_left] using hb

omit [DecidableEq ι] [DecidableEq κ] in
lemma mul (hF : SegmentRegular H θ F F' x C) (hG : SegmentRegular H θ G G' x D)
    {A B : ℝ} (hA : 0≤A) (hB : 0≤B)
    (hvF : ∀i k t, t∈Set.Icc (0:ℝ) 1→
      |F i (localArgs H θ x i+t • (localArgs H θ (flip x k) i-localArgs H θ x i))|≤A)
    (hvG : ∀i k t, t∈Set.Icc (0:ℝ) 1→
      |G i (localArgs H θ x i+t • (localArgs H θ (flip x k) i-localArgs H θ x i))|≤B) :
    SegmentRegular H θ (fun i u=>F i u*G i u)
      (fun i u=>F i u • G' i u+G i u • F' i u) x (A*D+B*C+2*C*D) := by
  refine ⟨by positivity [hF.nonneg,hG.nonneg],?_,?_,?_⟩
  · intro i k t ht
    exact (hF.deriv i k t ht).mul (hG.deriv i k t ht)
  · intro i k t ht
    let u:=localArgs H θ x i+t • (localArgs H θ (flip x k) i-localArgs H θ x i)
    have h₁ : ‖F i u • G' i u‖≤A*D := by
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul (hvF i k t ht) (hG.bound i k t ht) (norm_nonneg _) hA
    have h₂ : ‖G i u • F' i u‖≤B*C := by
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul (hvG i k t ht) (hF.bound i k t ht) (norm_nonneg _) hB
    have hh := (norm_add_le _ _).trans (add_le_add h₁ h₂)
    exact hh.trans (le_add_of_nonneg_right (by positivity [hF.nonneg,hG.nonneg]))
  · intro i k t ht
    let u:=localArgs H θ x i
    let v:=u+t • (localArgs H θ (flip x k) i-u)
    let d:=‖t • (localArgs H θ (flip x k) i-u)‖
    have hf : |F i v-F i u|≤C*d := hF.value_difference i k t ht
    have hg : |G i v-G i u|≤D*d := hG.value_difference i k t ht
    have hf' : ‖F' i v-F' i u‖≤C*d := hF.lip i k t ht
    have hg' : ‖G' i v-G' i u‖≤D*d := hG.lip i k t ht
    have hfu : ‖F' i u‖≤C := by simpa [u] using hF.bound i k 0 (by constructor <;> norm_num)
    have hgu : ‖G' i u‖≤D := by simpa [u] using hG.bound i k 0 (by constructor <;> norm_num)
    have he : (F i v • G' i v+G i v • F' i v)-(F i u • G' i u+G i u • F' i u)=
        (F i v • (G' i v-G' i u)+(F i v-F i u) • G' i u)+
        (G i v • (F' i v-F' i u)+(G i v-G i u) • F' i u) := by module
    change ‖(F i v • G' i v+G i v • F' i v)-(F i u • G' i u+G i u • F' i u)‖≤_
    rw [he]
    have h₁ : ‖F i v • (G' i v-G' i u)‖≤A*(D*d) := by
      rw [norm_smul,Real.norm_eq_abs]; exact mul_le_mul (hvF i k t ht) hg' (norm_nonneg _) hA
    have h₂ : ‖(F i v-F i u) • G' i u‖≤(C*d)*D := by
      rw [norm_smul,Real.norm_eq_abs]; exact mul_le_mul hf hgu (norm_nonneg _) (by positivity [hF.nonneg])
    have h₃ : ‖G i v • (F' i v-F' i u)‖≤B*(C*d) := by
      rw [norm_smul,Real.norm_eq_abs]; exact mul_le_mul (hvG i k t ht) hf' (norm_nonneg _) hB
    have h₄ : ‖(G i v-G i u) • F' i u‖≤(D*d)*C := by
      rw [norm_smul,Real.norm_eq_abs]; exact mul_le_mul hg hfu (norm_nonneg _) (by positivity [hG.nonneg])
    have hh := (norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add h₁ h₂))
      ((norm_add_le _ _).trans (add_le_add h₃ h₄)))
    exact hh.trans_eq (by dsimp only [d]; ring)

end SegmentRegular
end SKGapCutoff.Recipe

end
end

end OAI
