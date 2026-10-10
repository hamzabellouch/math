import Mathlib
import OAI.Probability.SKGap.Localization.ResidualAdmissibility

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
variable {n : ℕ} {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]

def SegmentValue (H : ι→VectorFields n) (θ : κ→Spin n→ℝ)
    (F : Fin n→Args (ι:=ι) (κ:=κ)→ℝ) (x : Spin n) (K : ℝ) : Prop :=
  ∀i k t,t∈Set.Icc (0:ℝ) 1→|F i (localArgs H θ x i+t • (localArgs H θ (flip x k) i-localArgs H θ x i))|≤K

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
lemma SegmentValue.at {H : ι→VectorFields n} {θ : κ→Spin n→ℝ}
    {F : Fin n→Args (ι:=ι) (κ:=κ)→ℝ} {x : Spin n} {K : ℝ}
    (h : SegmentValue H θ F x K) (i : Fin n) : |coefficient H θ F x i|≤K := by
  simpa [coefficient] using h i i 0 (by constructor <;> norm_num)

omit [DecidableEq ι] [DecidableEq κ] in
lemma segmentRegular_const (H : ι→VectorFields n) (θ : κ→Spin n→ℝ) (x : Spin n) (c : ℝ) :
    SegmentRegular H θ (fun _ _=>c) (fun _ _=>0) x 0 := by
  refine ⟨le_rfl,fun _ _ _ _=>hasFDerivAt_const _ _,?_,?_⟩
  · intros; simp
  · intros; simp

namespace OrdinaryData

structure CoefficientClass (D : OrdinaryData n ι κ σ) (N : ℕ) (x : Spin n) (K : ℝ) : Prop where
  one_le : 1≤K
  seedRegular : ∀a≤N,∀s,SegmentRegular D.H D.θ (D.seedFunction a s) (D.seedDerivative a s) x K
  auxRegular : ∀a≤N,∀b,SegmentRegular D.H D.θ (D.auxFunction a b) (D.auxDerivative a b) x K
  seedValue : ∀a≤N,∀s,SegmentValue D.H D.θ (D.seedFunction a s) x K
  auxValue : ∀a≤N,∀b,SegmentValue D.H D.θ (D.auxFunction a b) x K

omit [Fintype σ] in
lemma CoefficientClass.prefix {D : OrdinaryData n ι κ σ} {N A : ℕ} {x : Spin n} {K : ℝ}
    (h : D.CoefficientClass N x K) (ha : A≤N) : D.CoefficientClass A x K :=
  ⟨h.one_le,fun a hh=>h.seedRegular a (hh.trans ha),fun a hh=>h.auxRegular a (hh.trans ha),
    fun a hh=>h.seedValue a (hh.trans ha),fun a hh=>h.auxValue a (hh.trans ha)⟩

omit [Fintype σ] in
lemma CoefficientClass.appendProduct {D : OrdinaryData n ι κ σ} {N : ℕ} {x : Spin n} {K B : ℝ}
    (h : D.CoefficientClass N x K) (hB : 0≤B)
    (F : Fin n→Args (ι:=ι) (κ:=κ)→ℝ) (F')
    (hr : SegmentRegular D.H D.θ F F' x B) (hv : SegmentValue D.H D.θ F x B) :
    (D.appendProduct N F F').CoefficientClass (N+1) x (K+4*B*K) := by
  have hK : 0≤K := le_trans (by norm_num) h.one_le
  have hk : K≤K+4*B*K := le_add_of_nonneg_right (by positivity)
  have hbk : B*K≤K+4*B*K := by nlinarith [mul_nonneg hB hK]
  have hrk : B*K+K*B+2*B*K≤K+4*B*K := by nlinarith
  have hrold (G G') (hg : SegmentRegular D.H D.θ G G' x K) :
      SegmentRegular D.H D.θ G G' x (K+4*B*K) := hg.mono hk
  have hrnew (G G') (hg : SegmentRegular D.H D.θ G G' x K)
      (hgv : SegmentValue D.H D.θ G x K) :
      SegmentRegular D.H D.θ (fun i u=>F i u*G i u)
        (fun i u=>F i u • G' i u+G i u • F' i u) x (K+4*B*K) :=
    (hr.mul hg hB hK hv hgv).mono hrk
  refine ⟨h.one_le.trans hk,?_,?_,?_,?_⟩
  · intro a ha s
    by_cases he : a=N+1
    · subst a
      simpa only [OrdinaryData.appendProduct,ite_true] using hrnew _ _ (h.seedRegular N le_rfl s) (h.seedValue N le_rfl s)
    · have haN : a≤N := by omega
      simpa only [OrdinaryData.appendProduct,ite_eq_right he] using hrold _ _ (h.seedRegular a haN s)
  · intro a ha b
    by_cases he : a=N+1
    · subst a
      by_cases hb : b.val<N
      · simpa only [OrdinaryData.appendProduct,ite_true,dite_eq_left hb] using hrnew _ _ (h.auxRegular N le_rfl ⟨b.val,hb⟩) (h.auxValue N le_rfl ⟨b.val,hb⟩)
      · simpa only [OrdinaryData.appendProduct,ite_true,dite_eq_right hb] using (segmentRegular_const D.H D.θ x 0).mono (hK.trans hk)
    · have haN : a≤N := by omega
      simpa only [OrdinaryData.appendProduct,ite_eq_right he] using hrold _ _ (h.auxRegular a haN b)
  · intro a ha s i k t ht
    by_cases he : a=N+1
    · subst a
      simp only [OrdinaryData.appendProduct,ite_true,abs_mul]
      exact (mul_le_mul (hv i k t ht) (h.seedValue N le_rfl s i k t ht) (abs_nonneg _) hB).trans hbk
    · have haN : a≤N := by omega
      simpa only [OrdinaryData.appendProduct,ite_eq_right he] using (h.seedValue a haN s i k t ht).trans hk
  · intro a ha b i k t ht
    by_cases he : a=N+1
    · subst a
      by_cases hb : b.val<N
      · simp only [OrdinaryData.appendProduct,ite_true,dite_eq_left hb,abs_mul]
        exact (mul_le_mul (hv i k t ht) (h.auxValue N le_rfl ⟨b.val,hb⟩ i k t ht) (abs_nonneg _) hB).trans hbk
      · simpa only [OrdinaryData.appendProduct,ite_true,dite_eq_right hb,abs_zero] using hK.trans hk
    · have haN : a≤N := by omega
      simpa only [OrdinaryData.appendProduct,ite_eq_right he] using (h.auxValue a haN b i k t ht).trans hk

omit [Fintype σ] in
lemma CoefficientClass.appendAuxiliary {M : ℕ} {D : OrdinaryData n (Fin M) κ σ}
    {N : ℕ} {x : Spin n} {K : ℝ} (h : D.CoefficientClass N x K) :
    (D.appendAuxiliary N).CoefficientClass (N+1) x K := by
  have hK : 0≤K := le_trans (by norm_num) h.one_le
  refine ⟨h.one_le,?_,?_,?_,?_⟩
  · intro a ha s
    by_cases he : a=N+1
    · subst a
      simpa only [OrdinaryData.appendAuxiliary,ite_true] using (segmentRegular_const D.H D.θ x 0).mono hK
    · have haN : a≤N := by omega
      simpa only [OrdinaryData.appendAuxiliary,ite_eq_right he] using h.seedRegular a haN s
  · intro a ha b
    by_cases he : a=N+1
    · subst a
      simp only [OrdinaryData.appendAuxiliary,ite_true]
      exact (segmentRegular_const D.H D.θ x (if b.val=N then 1 else 0)).mono hK
    · have haN : a≤N := by omega
      simpa only [OrdinaryData.appendAuxiliary,ite_eq_right he] using h.auxRegular a haN b
  · intro a ha s i k t ht
    by_cases he : a=N+1
    · simp [OrdinaryData.appendAuxiliary,he,hK]
    · have haN : a≤N := by omega
      simpa only [OrdinaryData.appendAuxiliary,ite_eq_right he] using h.seedValue a haN s i k t ht
  · intro a ha b i k t ht
    by_cases he : a=N+1
    · simp only [OrdinaryData.appendAuxiliary,ite_eq_left he]
      split_ifs
      · simpa using h.one_le
      · simpa using hK
    · have haN : a≤N := by omega
      simpa only [OrdinaryData.appendAuxiliary,ite_eq_right he] using h.auxValue a haN b i k t ht

end OrdinaryData
end SKGapCutoff.Recipe

end
end

end OAI
