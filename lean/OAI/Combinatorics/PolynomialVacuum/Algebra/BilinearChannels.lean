import OAI.Combinatorics.PolynomialVacuum.Algebra.Ring
import OAI.Combinatorics.PolynomialVacuum.Algebra.Projectors

namespace OAI

namespace PolynomialVacuumAlgebra

noncomputable def eigenZero (x y : ℂ) : ℂ := (t^2*y-x)*(T*x-y)
noncomputable def eigenOne (x y : ℂ) : ℂ := (T*y-x)*(t^2*x-y)
noncomputable def eigenTwo (x y : ℂ) : ℂ := (t^2*y-x)*(T*y-x)

def ScalarBilinearExchange (e : ℂ → ℂ → ℂ) (a b c d : ℂ) : Prop :=
  ∀ x y, e x y*(a+x*b+y*c+x*y*d)=eigenOne x y*(a+y*b+x*c+x*y*d)

theorem bilinearZero_a (a b c d : ℂ) (h : ScalarBilinearExchange eigenZero a b c d) : a=0 := by
  have h0 := h (1) (0)
  simp only [eigenZero,eigenOne,T,t] at h0
  have h1 := h (-1) (0)
  simp only [eigenZero,eigenOne,T,t] at h1
  linear_combination (norm := skip) ((1/4:ℂ)+(1/4:ℂ)*q^2-(1/4:ℂ)*q^4-(1/4:ℂ)*q^6)*h0+((1/4:ℂ)+(1/4:ℂ)*q^2-(1/4:ℂ)*q^4-(1/4:ℂ)*q^6)*h1
  vacuum_ring_finish

theorem bilinearZero_b (a b c d : ℂ) (h : ScalarBilinearExchange eigenZero a b c d) : b=0 := by
  have h0 := h (1) (0)
  simp only [eigenZero,eigenOne,T,t] at h0
  have h1 := h (-1) (0)
  simp only [eigenZero,eigenOne,T,t] at h1
  have h4 := h (1) (2)
  simp only [eigenZero,eigenOne,T,t] at h4
  have h5 := h (-1) (-2)
  simp only [eigenZero,eigenOne,T,t] at h5
  linear_combination (norm := skip) (-(7/8:ℂ)+(1/4:ℂ)*q^2+(7/8:ℂ)*q^4+(7/8:ℂ)*q^6)*h0+((7/8:ℂ)-(1/4:ℂ)*q^2-(7/8:ℂ)*q^4-(7/8:ℂ)*q^6)*h1+(-(1/8:ℂ)+(1/8:ℂ)*q^4+(1/8:ℂ)*q^6)*h4+((1/8:ℂ)-(1/8:ℂ)*q^4-(1/8:ℂ)*q^6)*h5
  vacuum_ring_finish

theorem bilinearZero_c (a b c d : ℂ) (h : ScalarBilinearExchange eigenZero a b c d) : c=0 := by
  have h0 := h (1) (0)
  simp only [eigenZero,eigenOne,T,t] at h0
  have h1 := h (-1) (0)
  simp only [eigenZero,eigenOne,T,t] at h1
  have h4 := h (1) (2)
  simp only [eigenZero,eigenOne,T,t] at h4
  have h5 := h (-1) (-2)
  simp only [eigenZero,eigenOne,T,t] at h5
  linear_combination (norm := skip) (-(7/8:ℂ)-(7/8:ℂ)*q^2-(1/4:ℂ)*q^4+(7/8:ℂ)*q^6)*h0+((7/8:ℂ)+(7/8:ℂ)*q^2+(1/4:ℂ)*q^4-(7/8:ℂ)*q^6)*h1+(-(1/8:ℂ)-(1/8:ℂ)*q^2+(1/8:ℂ)*q^6)*h4+((1/8:ℂ)+(1/8:ℂ)*q^2-(1/8:ℂ)*q^6)*h5
  vacuum_ring_finish

theorem bilinearZero_d (a b c d : ℂ) (h : ScalarBilinearExchange eigenZero a b c d) : d=0 := by
  have h0 := h (1) (0)
  simp only [eigenZero,eigenOne,T,t] at h0
  have h1 := h (-1) (0)
  simp only [eigenZero,eigenOne,T,t] at h1
  have h4 := h (1) (2)
  simp only [eigenZero,eigenOne,T,t] at h4
  have h5 := h (-1) (-2)
  simp only [eigenZero,eigenOne,T,t] at h5
  linear_combination (norm := skip) (-(1/8:ℂ)-(1/8:ℂ)*q^2+(1/8:ℂ)*q^4+(1/8:ℂ)*q^6)*h0+(-(1/8:ℂ)-(1/8:ℂ)*q^2+(1/8:ℂ)*q^4+(1/8:ℂ)*q^6)*h1+(-(1/24:ℂ)-(1/24:ℂ)*q^2+(1/24:ℂ)*q^4+(1/24:ℂ)*q^6)*h4+(-(1/24:ℂ)-(1/24:ℂ)*q^2+(1/24:ℂ)*q^4+(1/24:ℂ)*q^6)*h5
  vacuum_ring_finish

theorem bilinearOne_bc (a b c d : ℂ) (h : ScalarBilinearExchange eigenOne a b c d) : b=c := by
  have h0 := h (1) (0)
  simp only [eigenOne,eigenOne,T,t] at h0
  linear_combination (norm := skip) (q^4)*h0
  vacuum_ring_finish

theorem bilinearTwo_a (a b c d : ℂ) (h : ScalarBilinearExchange eigenTwo a b c d) : a=0 := by
  have h0 := h (1) (0)
  simp only [eigenTwo,eigenOne,T,t] at h0
  have h1 := h (-1) (0)
  simp only [eigenTwo,eigenOne,T,t] at h1
  linear_combination (norm := skip) ((1/4:ℂ)-(1/4:ℂ)*q^4)*h0+((1/4:ℂ)-(1/4:ℂ)*q^4)*h1
  vacuum_ring_finish

theorem bilinearTwo_d (a b c d : ℂ) (h : ScalarBilinearExchange eigenTwo a b c d) : d=0 := by
  have h0 := h (1) (0)
  simp only [eigenTwo,eigenOne,T,t] at h0
  have h1 := h (-1) (0)
  simp only [eigenTwo,eigenOne,T,t] at h1
  have h4 := h (1) (2)
  simp only [eigenTwo,eigenOne,T,t] at h4
  linear_combination (norm := skip) (-(1/2:ℂ)+(1/2:ℂ)*q^4)*h0+((1/4:ℂ)-(1/4:ℂ)*q^4)*h1+((3/68:ℂ)-(5/34:ℂ)*q^2+(5/68:ℂ)*q^4+(3/34:ℂ)*q^6)*h4
  vacuum_ring_finish

theorem bilinearTwo_bc (a b c d : ℂ) (h : ScalarBilinearExchange eigenTwo a b c d) : b= -(t^2)*c := by
  have h0 := h (1) (0)
  simp only [eigenTwo,eigenOne,T,t] at h0
  have h1 := h (-1) (0)
  simp only [eigenTwo,eigenOne,T,t] at h1
  unfold t
  linear_combination (norm := skip) ((1/2:ℂ))*h0+(-(1/2:ℂ))*h1
  vacuum_ring_finish

end PolynomialVacuumAlgebra

end OAI
