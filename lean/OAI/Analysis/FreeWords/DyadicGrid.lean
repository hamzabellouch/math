import Mathlib
import OAI.Analysis.FreeWords.ProjectionSubdivision

namespace OAI

noncomputable section

namespace KKProjectionSupport

open KKTraceTransfer KKUltraTrace KKFactorSupport KKFreeLiftFrontier

open scoped ComplexOrder

noncomputable section

def BitWords : ℕ → Type
  | 0 => Unit
  | n+1 => BitWords n × Bool

instance bitWordsFintype (n : ℕ) : Fintype (BitWords n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ n ih => exact @instFintypeProd _ _ ih inferInstance

instance bitWordsDecEq (n : ℕ) : DecidableEq (BitWords n) := Classical.decEq _

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance dyadicGridConcreteOrder (M : VonNeumannAlgebra H) : PartialOrder (ConcreteAlgebra M) := concreteOrder M

local instance dyadicGridConcretePreorder (M : VonNeumannAlgebra H) : Preorder (ConcreteAlgebra M) := (concreteOrder M).toPreorder

local instance dyadicGridConcreteLE (M : VonNeumannAlgebra H) : LE (ConcreteAlgebra M) := (concreteOrder M).toLE

local instance dyadicGridConcreteSOR (M : VonNeumannAlgebra H) : StarOrderedRing (ConcreteAlgebra M) := concreteSOR M

structure DyadicGrid (M : VonNeumannAlgebra H) (τ : FaithfulNormalTrace M) (n : ℕ) where
  p : BitWords n → ConcreteAlgebra M
  proj : ∀ w, IsStarProjection (p w)
  orth : ∀ v w, v≠w → p v*p w=0
  sum : ∑ w, p w=1
  trace : ∀ w, τ.map (p w)=(((1/2:ℝ)^n : ℝ):ℂ)

def gridZero (M : VonNeumannAlgebra H) (τ : FaithfulNormalTrace M) : DyadicGrid M τ 0 where
  p _ := 1
  proj _ := IsStarProjection.one _
  orth v w h := by exact (h (by cases v; cases w; rfl)).elim
  sum := by change ∑ _ : Unit, (1:ConcreteAlgebra M)=1; simp
  trace w := by simp only [pow_zero,Complex.ofReal_one,τ.normalized]

theorem grid_refine (M : VonNeumannAlgebra H) (τ : FaithfulNormalTrace M)
    (hD : IsDiffuse M) {n : ℕ} (G : DyadicGrid M τ n) :
    ∃ G' : DyadicGrid M τ (n+1), ∀ w,
      G'.p (w,true)+G'.p (w,false)=G.p w := by
  classical
  have ht : 0 ≤ (1/2:ℝ)^n := le_of_lt (pow_pos (by norm_num) _)
  have hex (w : BitWords n) : ∃ q : ConcreteAlgebra M, IsStarProjection q ∧ q*G.p w=q ∧
      τ.map q=(((1/2:ℝ)^n/2 : ℝ):ℂ) := by
    apply projection_with_trace M τ hD (G.p w) (G.proj w) _ (div_nonneg ht (by norm_num))
    rw [G.trace,Complex.ofReal_re]
    linarith
  choose q hq hqp hτq using hex
  have hle (w) : q w ≤ G.p w := ((hq w).le_iff_mul_eq_left (G.proj w)).mpr (hqp w)
  let f : BitWords (n+1) → ConcreteAlgebra M := fun w => if w.2 then q w.1 else G.p w.1-q w.1
  have hf (w : BitWords (n+1)) : IsStarProjection (f w) := by
    rcases w with ⟨w,b⟩; cases b
    · exact ((hq w).le_iff_sub (G.proj w)).mp (hle w)
    · exact hq w
  have hfp (w : BitWords (n+1)) : f w ≤ G.p w.1 := by
    rcases w with ⟨w,b⟩; cases b
    · exact sub_le_self _ (hq w).nonneg
    · exact hle w
  have hff (v w : BitWords (n+1)) (hvw : v≠w) : f v*f w=0 := by
    by_cases hfst : v.1=w.1
    · rcases v with ⟨v,b⟩; rcases w with ⟨w,c⟩; dsimp at hfst; subst w
      cases b <;> cases c
      · exact (hvw rfl).elim
      · change (G.p v-q v)*q v=0
        rw [sub_mul,((hq v).le_iff_mul_eq_right (G.proj v)).mp (hle v),(hq v).isIdempotentElem.eq,sub_self]
      · change q v*(G.p v-q v)=0
        rw [mul_sub,hqp,(hq v).isIdempotentElem.eq,sub_self]
      · exact (hvw rfl).elim
    · calc
        f v*f w = (f v*G.p v.1)*(G.p w.1*f w) := by
          rw [((hf v).le_iff_mul_eq_left (G.proj _)).mp (hfp v),((hf w).le_iff_mul_eq_right (G.proj _)).mp (hfp w)]
        _ = f v*(G.p v.1*G.p w.1)*f w := by simp only [mul_assoc]
        _ = 0 := by rw [G.orth _ _ hfst,mul_zero,zero_mul]
  have hfs (w : BitWords n) : f (w,true)+f (w,false)=G.p w := by dsimp [f]; abel
  have hsum : ∑ w, f w=1 := by
    change ∑ w : BitWords n × Bool, f w=1
    rw [Fintype.sum_prod_type]
    calc
      _ = ∑ w, G.p w := Finset.sum_congr rfl fun w _ => (Fintype.sum_bool _).trans (hfs w)
      _ = 1 := G.sum
  have hfτ (w : BitWords (n+1)) : τ.map (f w)=(((1/2:ℝ)^(n+1):ℝ):ℂ) := by
    rcases w with ⟨w,b⟩
    have hr : (1/2:ℝ)^(n+1)=(1/2:ℝ)^n/2 := by rw [pow_succ]; ring
    rw [hr]
    cases b
    · change τ.map (G.p w-q w)=_
      rw [map_sub,G.trace,hτq]
      push_cast
      ring
    · exact hτq w
  exact ⟨⟨f,hf,hff,hsum,hfτ⟩,hfs⟩

def dyadicGrid (M : VonNeumannAlgebra H) (τ : FaithfulNormalTrace M) (hD : IsDiffuse M) :
    (n : ℕ) → DyadicGrid M τ n
  | 0 => gridZero M τ
  | n+1 => (grid_refine M τ hD (dyadicGrid M τ hD n)).choose

theorem dyadicGrid_refine (M : VonNeumannAlgebra H) (τ : FaithfulNormalTrace M)
    (hD : IsDiffuse M) (n : ℕ) (w : BitWords n) :
    (dyadicGrid M τ hD (n+1)).p (w,true)+(dyadicGrid M τ hD (n+1)).p (w,false)=
      (dyadicGrid M τ hD n).p w :=
  (grid_refine M τ hD (dyadicGrid M τ hD n)).choose_spec w

end

end KKProjectionSupport
end

end OAI
