import OAI.Analysis.Triangular.Signs.DeletedQuotient
import OAI.Analysis.Triangular.Signs.DeletedExponential

namespace OAI

noncomputable section
open scoped BigOperators
open Complex
namespace AtomicTriangular.Construction

def complexDeleted (F : ℕ → ℝ → ℂ) (m v : ℝ) : ℂ :=
  if v=0 then F 2 m/2 else (F 0 (m+v)-F 0 m-(v:ℂ)*F 1 m)/(v:ℂ)^2
def complexTaylor (F : ℕ → ℝ → ℂ) (m v : ℝ) : ℂ :=
  ∑ j ∈ Finset.range 21,F (j+2) m*(v:ℂ)^j/((j+2).factorial:ℂ)
lemma complexDeleted_re (F : ℕ → ℝ → ℂ) (f : ℝ → ℝ) (m v : ℝ)
    (h0 : ∀ s,(F 0 s).re=f s) (h1 : (F 1 m).re=deriv f m) (h2 : (F 2 m).re=iteratedDeriv 2 f m) :
    (complexDeleted F m v).re=deletedSecond f m (m+v) := by
  by_cases hv : v=0
  · subst v
    simp [complexDeleted,deletedSecond,h2]
  · have hs : m+v≠m := by intro hh; apply hv; linarith
    simp only [complexDeleted,ite_eq_right hv,deletedSecond,ite_eq_right hs,show m+v-m=v by ring,
      ←Complex.ofReal_pow,Complex.div_ofReal_re,sub_re,mul_re,ofReal_re,ofReal_im,zero_mul,sub_zero,h0,h1]
    ring
lemma complexDeleted_add (F G : ℕ → ℝ → ℂ) (m v : ℝ) :
    complexDeleted (fun k s => F k s+G k s) m v=complexDeleted F m v+complexDeleted G m v := by
  unfold complexDeleted
  split_ifs <;> ring
lemma complexDeleted_mul (a : ℂ) (F : ℕ → ℝ → ℂ) (m v : ℝ) :
    complexDeleted (fun k s => a*F k s) m v=a*complexDeleted F m v := by
  unfold complexDeleted
  split_ifs <;> ring
lemma complexDeleted_sum {ι : Type*} (S : Finset ι) (F : ι → ℕ → ℝ → ℂ) (m v : ℝ) :
    complexDeleted (fun k s => ∑ i∈S,F i k s) m v=∑ i∈S,complexDeleted (F i) m v := by
  unfold complexDeleted
  by_cases hv : v=0
  · simp only [hv,↓reduceIte,Finset.sum_div]
  · simp only [ite_eq_right hv,sub_div,Finset.sum_div,Finset.sum_sub_distrib,Finset.mul_sum]
lemma complexTaylor_add (F G : ℕ → ℝ → ℂ) (m v : ℝ) :
    complexTaylor (fun k s => F k s+G k s) m v=complexTaylor F m v+complexTaylor G m v := by
  simp [complexTaylor,add_mul,add_div,Finset.sum_add_distrib]
lemma complexTaylor_mul (a : ℂ) (F : ℕ → ℝ → ℂ) (m v : ℝ) :
    complexTaylor (fun k s => a*F k s) m v=a*complexTaylor F m v := by
  simp [complexTaylor,Finset.mul_sum,mul_assoc,mul_div_assoc]
lemma complexTaylor_sum {ι : Type*} (S : Finset ι) (F : ι → ℕ → ℝ → ℂ) (m v : ℝ) :
    complexTaylor (fun k s => ∑ i∈S,F i k s) m v=∑ i∈S,complexTaylor (F i) m v := by
  simp only [complexTaylor,Finset.sum_mul,Finset.sum_div]
  exact Finset.sum_comm
lemma complexDeleted_exp (w : ℂ) (m v : ℝ) :
    complexDeleted (fun k s => exp (w*(s:ℂ))*w^k) m v=Envelope.expDeleted w m v := by
  unfold complexDeleted Envelope.expDeleted
  split_ifs <;> simp only [pow_zero,pow_one,mul_one]
  ring
lemma complexTaylor_exp (w : ℂ) (m v : ℝ) :
    complexTaylor (fun k s => exp (w*(s:ℂ))*w^k) m v=Envelope.expDeletedTaylor w m v := by
  simp only [complexTaylor,Envelope.expDeletedTaylor,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_add,mul_pow]
  ring
end AtomicTriangular.Construction
end

end OAI
