import OAI.Probability.BenjaminiSchramm.SlabFirstVisit

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

lemma integer_half_band (k m : ℤ) :
    ((m : ℝ)-1/2 ≤ (k : ℝ) ∧ (k : ℝ) ≤ (m : ℝ)-1/2+1) ↔ k=m := by
  constructor
  · rintro ⟨hlo,hhi⟩
    have h₁ : (m : ℝ)-1 < k := by linarith
    have h₂ : (k : ℝ) < (m : ℝ)+1 := by linarith
    have h₁' : m-1 < k := by exact_mod_cast h₁
    have h₂' : k < m+1 := by exact_mod_cast h₂
    omega
  · rintro rfl
    constructor <;> linarith

lemma integer_half_ceiling (k m : ℤ) :
    ((k : ℝ) ≤ (m : ℝ)-1/2+1) ↔ k ≤ m := by
  constructor
  · intro h
    have hh : (k : ℝ) < (m : ℝ)+1 := by linarith
    have hh' : k < m+1 := by exact_mod_cast hh
    omega
  · intro h
    have hh : (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast h
    linarith

theorem integer_first_layer_moment_bound [Countable V] [Countable E]
    (f : V → ℤ)
    (hjump : ∀ e u v, u ∈ G e → v ∈ G e → f v ≤ f u+1 ∧ f u ≤ f v+1)
    (I : Set E) (A : Set V) (p : unitInterval) (x : V) (m : ℤ)
    (hx : f x < m) (hA : ∀ y ∈ A, m ≤ f y) :
    (∫⁻ ω, restrictedLayerCount G I A ω x ∂law p) ≤
      ∑' z, (if f z=m then
        law p {ω | Conn G (ω ∩ (I ∩ internalEdges G {v | f v ≤ m})) x z} else 0) *
          (∫⁻ ω, restrictedLayerCount G I A ω z ∂law p) := by
  have hj : ∀ e u v, u ∈ G e → v ∈ G e → |(f v : ℝ)-(f u : ℝ)| ≤ 1 := by
    intro e u v hu hv
    obtain ⟨h₁,h₂⟩ := hjump e u v hu hv
    have h₁' : (f v : ℝ) ≤ (f u : ℝ)+1 := by exact_mod_cast h₁
    have h₂' : (f u : ℝ) ≤ (f v : ℝ)+1 := by exact_mod_cast h₂
    rw [abs_le]
    constructor <;> linarith
  have hx' : (f x : ℝ) < (m : ℝ)-1/2 := by
    have hh : f x ≤ m-1 := by omega
    have hh' : (f x : ℝ) ≤ (m : ℝ)-1 := by exact_mod_cast hh
    linarith
  have hA' : ∀ y ∈ A, (m : ℝ)-1/2 ≤ (f y : ℝ) := by
    intro y hy
    have hh : (m : ℝ) ≤ (f y : ℝ) := by exact_mod_cast hA y hy
    linarith
  have hh := first_height_layer_moment_bound G (fun v => (f v : ℝ)) 1 ((m : ℝ)-1/2)
    (by norm_num) hj I A p x hx' hA'
  have hD : {v : V | (f v : ℝ) ≤ (m : ℝ)-1/2+1} = {v | f v ≤ m} := by
    ext v
    exact integer_half_ceiling (f v) m
  simpa only [hD,integer_half_band] using hh

end Percolation.BenjaminiSchramm

end

end OAI
