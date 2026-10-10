import OAI.Analysis.KadisonKastler.StateBicentralizerStar

namespace OAI

/-! # Algebra operations on the faithful state bicentralizer -/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem stateBicentralizerMember_zero (ξ : H) :
    stateBicentralizerMember (M := M) ξ 0 := by
  intro x hx η
  simpa only [zero_mul,mul_zero,sub_self,ZeroMemClass.coe_zero,zero_apply] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : H)) atTop (𝓝 0))

theorem stateBicentralizerMember_one (ξ : H) :
    stateBicentralizerMember (M := M) ξ 1 := by
  intro x hx η
  simpa only [one_mul,mul_one,sub_self,ZeroMemClass.coe_zero,zero_apply] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : H)) atTop (𝓝 0))

theorem stateBicentralizerMember_add (ξ : H) {a b : Algebra M}
    (ha : stateBicentralizerMember ξ a) (hb : stateBicentralizerMember ξ b) :
    stateBicentralizerMember ξ (a+b) := by
  intro x hx η
  have he (n : ℕ) : ((a+b)*(x n)-(x n)*(a+b)).val η=
      (a*(x n)-(x n)*a).val η+(b*(x n)-(x n)*b).val η := by
    have h : (a+b)*(x n)-(x n)*(a+b)=
        (a*(x n)-(x n)*a)+(b*(x n)-(x n)*b) := by
      rw [add_mul,mul_add]; abel
    rw [h]; rfl
  simpa only [he,add_zero] using (ha x hx η).add (hb x hx η)

theorem stateBicentralizerMember_smul (ξ : H) (c : ℂ) {a : Algebra M}
    (ha : stateBicentralizerMember ξ a) : stateBicentralizerMember ξ (c • a) := by
  intro x hx η
  have he (n : ℕ) : ((c • a)*(x n)-(x n)*(c • a)).val η=
      c • (a*(x n)-(x n)*a).val η := by
    rw [smul_mul_assoc,mul_smul_comm,← smul_sub]; rfl
  simpa only [he,smul_zero] using (ha x hx η).const_smul c

theorem stateBicentralizerMember_mul (ξ : H) {a b : Algebra M}
    (ha : stateBicentralizerMember ξ a) (hb : stateBicentralizerMember ξ b) :
    stateBicentralizerMember ξ (a*b) := by
  intro x hx η
  have he (n : ℕ) : ((a*b)*(x n)-(x n)*(a*b)).val η=
      a.val ((b*(x n)-(x n)*b).val η)+(a*(x n)-(x n)*a).val (b.val η) := by
    have h : (a*b)*(x n)-(x n)*(a*b)=
        a*(b*(x n)-(x n)*b)+(a*(x n)-(x n)*a)*b := by
      rw [mul_sub,sub_mul]; simp only [mul_assoc]; abel
    rw [h]; rfl
  have ht := a.val.continuous.tendsto (0 : H) |>.comp (hb x hx η)
  simpa only [Function.comp_def,map_zero,he,add_zero] using ht.add (ha x hx (b.val η))

def stateBicentralizerAlgebra (ξ : H)
    (hsep : Function.Injective (algebraVectorMap M ξ)) : StarSubalgebra ℂ (Algebra M) where
  carrier := {a | stateBicentralizerMember ξ a}
  zero_mem' := stateBicentralizerMember_zero ξ
  one_mem' := stateBicentralizerMember_one ξ
  add_mem' := stateBicentralizerMember_add ξ
  mul_mem' := stateBicentralizerMember_mul ξ
  algebraMap_mem' c := by
    change stateBicentralizerMember ξ (algebraMap ℂ (Algebra M) c)
    simpa only [Algebra.algebraMap_eq_smul_one] using
      stateBicentralizerMember_smul ξ c (stateBicentralizerMember_one ξ)
  star_mem' {a} ha := stateBicentralizerMember_star ξ hsep a ha

end

end KadisonKastler

end OAI
