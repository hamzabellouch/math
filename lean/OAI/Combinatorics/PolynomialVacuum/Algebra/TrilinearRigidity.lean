import OAI.Combinatorics.PolynomialVacuum.Algebra.BitCoefficients
import OAI.Combinatorics.PolynomialVacuum.Algebra.VectorBilinear

namespace OAI

namespace PolynomialVacuumAlgebra
open Classical

abbrev TripleSpectral := ℂ → ℂ → ℂ → Spin → Spin → Spin → ℂ

@[simp] theorem bitCoefficient_apply {ι : Type*} (b : Bool) (f : ℂ → ι → ℂ) (a : ι) :
    bitCoefficient b f a=bitCoefficient b (fun x => f x a) := by cases b <;> rfl

theorem affine_pi {ι : Type*} (f : ℂ → ι → ℂ)
    (h : ∀ a, AffineFunction (fun x => f x a)) : AffineFunction f := by
  intro x; funext a; exact h a x

def PairFunctionExchange (f : ℂ → ℂ → Pair → ℂ) : Prop :=
  ∀ x y, (exchangeNumerator x y).mulVec (f x y)=eigenOne x y • f y x

theorem bitCoefficient_pairExchange (i : Bool) (f : ℂ → ℂ → ℂ → Pair → ℂ)
    (he : ∀ z, PairFunctionExchange (fun x y => f x y z)) :
    PairFunctionExchange (fun x y => bitCoefficient i (f x y)) := by
  intro x y
  cases i
  · exact he 0 x y
  · simp only [bitCoefficient_true,Matrix.mulVec_sub]
    rw [he 1 x y,he 0 x y,smul_sub]

theorem bilinear_coeff_exchange (f : ℂ → ℂ → Pair → ℂ)
    (hx : ∀ y, AffineFunction (fun x => f x y)) (hy : ∀ x, AffineFunction (f x))
    (he : PairFunctionExchange f) :
    VectorBilinearExchange (biCoefficient f false false) (biCoefficient f true false)
      (biCoefficient f false true) (biCoefficient f true true) := by
  intro x y
  have hh := he x y
  rw [bilinear_expansion f hx hy x y,bilinear_expansion f hx hy y x] at hh
  simpa only [mul_comm x y] using hh

noncomputable def spectralBits (f : TripleSpectral) : BitTensorFamily :=
  fun i j k a b c => triCoefficient (fun x y z => f x y z a b c) i j k

theorem bitCoefficient_support (s : Spin) (f : ℂ → ℂ)
    (hp : s=Spin.plus → ∀ x, f x=f 0) (hm : s=Spin.minus → f 0=0)
    (i : Bool) (hi : ¬allowedSpin i s) : bitCoefficient i f=0 := by
  cases s <;> cases i <;> simp [allowedSpin,occupiedSpin] at hi
  · rw [bitCoefficient_true,hp rfl 1,sub_self]
  · exact hm rfl

theorem spectralBits_support (f : TripleSpectral)
    (hp1 : ∀ a b c, a=Spin.plus → ∀ x y z, f x y z a b c=f 0 y z a b c)
    (hp2 : ∀ a b c, b=Spin.plus → ∀ x y z, f x y z a b c=f x 0 z a b c)
    (hp3 : ∀ a b c, c=Spin.plus → ∀ x y z, f x y z a b c=f x y 0 a b c)
    (hm1 : ∀ a b c, a=Spin.minus → ∀ y z, f 0 y z a b c=0)
    (hm2 : ∀ a b c, b=Spin.minus → ∀ x z, f x 0 z a b c=0)
    (hm3 : ∀ a b c, c=Spin.minus → ∀ x y, f x y 0 a b c=0) :
    ∀ i j k a b c, ¬(allowedSpin i a ∧ allowedSpin j b ∧ allowedSpin k c) → spectralBits f i j k a b c=0 := by
  intro i j k a b c h
  simp only [spectralBits,triCoefficient]
  by_cases ha : allowedSpin i a
  · by_cases hb : allowedSpin j b
    · have hc : ¬allowedSpin k c := by tauto
      have he (x y : ℂ) : bitCoefficient k (fun z => f x y z a b c)=0 :=
        bitCoefficient_support c _ (fun hp z => hp3 a b c hp x y z)
          (fun hm => hm3 a b c hm x y) k hc
      simp only [he,bitCoefficient_zero]
    · simp_rw [bitCoefficient_comm j k]
      have he (x z : ℂ) : bitCoefficient j (fun y => f x y z a b c)=0 :=
        bitCoefficient_support b _ (fun hp y => hp2 a b c hp x y z)
          (fun hm => hm2 a b c hm x z) j hb
      simp only [he,bitCoefficient_zero]
  · rw [bitCoefficient_comm i j]
    simp_rw [bitCoefficient_comm i k]
    have he (y z : ℂ) : bitCoefficient i (fun x => f x y z a b c)=0 :=
      bitCoefficient_support a _ (fun hp x => hp1 a b c hp x y z)
        (fun hm => hm1 a b c hm y z) i ha
    simp only [he,bitCoefficient_zero]

theorem spectralBits_first_pair (f : TripleSpectral) (k : Bool) (c : Spin) :
    (fun i j ab => spectralBits f i j k ab.1 ab.2 c)=
      (fun i j => biCoefficient (fun x y => bitCoefficient k (fun z (ab : Pair) => f x y z ab.1 ab.2 c)) i j) := by
  funext i j ab
  simp only [spectralBits,triCoefficient,biCoefficient,bitCoefficient_apply]

theorem spectralBits_last_pair (f : TripleSpectral) (i : Bool) (a : Spin) :
    (fun j k bc => spectralBits f i j k a bc.1 bc.2)=
      (fun j k => biCoefficient (fun y z => bitCoefficient i (fun x (bc : Pair) => f x y z a bc.1 bc.2)) j k) := by
  funext j k bc
  simp only [spectralBits,triCoefficient,biCoefficient,bitCoefficient_apply]
  rw [bitCoefficient_comm i j]
  simp_rw [bitCoefficient_comm i k]

theorem spectralBits_channels (f : TripleSpectral)
    (hx : ∀ y z a b c, AffineFunction (fun x => f x y z a b c))
    (hy : ∀ x z a b c, AffineFunction (fun y => f x y z a b c))
    (hz : ∀ x y a b c, AffineFunction (fun z => f x y z a b c))
    (hex1 : ∀ z c, PairFunctionExchange (fun x y ab => f x y z ab.1 ab.2 c))
    (hex2 : ∀ x a, PairFunctionExchange (fun y z bc => f x y z a bc.1 bc.2)) :
    (∀ i k c, Pone.mulVec (fun ab => spectralBits f i i k ab.1 ab.2 c)=fun ab => spectralBits f i i k ab.1 ab.2 c) ∧
    (∀ i k a, Pone.mulVec (fun bc => spectralBits f i k k a bc.1 bc.2)=fun bc => spectralBits f i k k a bc.1 bc.2) ∧
    (∀ i j k c, ∑ ab : Pair, cup ab*spectralBits f i j k ab.1 ab.2 c=0) ∧
    (∀ i j k a, ∑ bc : Pair, cup bc*spectralBits f i j k a bc.1 bc.2=0) ∧
    (∀ i a, bitSwap.mulVec (fun bc => spectralBits f i false true a bc.1 bc.2)=fun bc => spectralBits f i true false a bc.1 bc.2) := by
  have hfirst (k : Bool) (c : Spin) :
      VectorBilinearExchange (fun ab => spectralBits f false false k ab.1 ab.2 c)
        (fun ab => spectralBits f true false k ab.1 ab.2 c)
        (fun ab => spectralBits f false true k ab.1 ab.2 c)
        (fun ab => spectralBits f true true k ab.1 ab.2 c) := by
    let g := fun x y => bitCoefficient k (fun z (ab : Pair) => f x y z ab.1 ab.2 c)
    have hgx : ∀ y, AffineFunction (fun x => g x y) := by
      intro y; apply affine_pi; intro ab
      simp only [g,bitCoefficient_apply]
      exact affine_bitCoefficient k _ (fun z => hx y z ab.1 ab.2 c)
    have hgy : ∀ x, AffineFunction (g x) := by
      intro x; apply affine_pi; intro ab
      simp only [g,bitCoefficient_apply]
      exact affine_bitCoefficient k _ (fun z => hy x z ab.1 ab.2 c)
    have he := bilinear_coeff_exchange g hgx hgy (bitCoefficient_pairExchange k _ (fun z => hex1 z c))
    have hc (i j : Bool) : (fun ab => spectralBits f i j k ab.1 ab.2 c)=biCoefficient g i j :=
      congrFun (congrFun (spectralBits_first_pair f k c) i) j
    rw [←hc false false,←hc true false,←hc false true,←hc true true] at he
    exact he
  have hlast (i : Bool) (a : Spin) :
      VectorBilinearExchange (fun bc => spectralBits f i false false a bc.1 bc.2)
        (fun bc => spectralBits f i true false a bc.1 bc.2)
        (fun bc => spectralBits f i false true a bc.1 bc.2)
        (fun bc => spectralBits f i true true a bc.1 bc.2) := by
    let g := fun y z => bitCoefficient i (fun x (bc : Pair) => f x y z a bc.1 bc.2)
    have hgy : ∀ z, AffineFunction (fun y => g y z) := by
      intro z; apply affine_pi; intro bc
      simp only [g,bitCoefficient_apply]
      exact affine_bitCoefficient i _ (fun x => hy x z a bc.1 bc.2)
    have hgz : ∀ y, AffineFunction (g y) := by
      intro y; apply affine_pi; intro bc
      simp only [g,bitCoefficient_apply]
      exact affine_bitCoefficient i _ (fun x => hz x y a bc.1 bc.2)
    have he := bilinear_coeff_exchange g hgy hgz (bitCoefficient_pairExchange i _ (fun x => hex2 x a))
    have hc (j k : Bool) : (fun bc => spectralBits f i j k a bc.1 bc.2)=biCoefficient g j k :=
      congrFun (congrFun (spectralBits_last_pair f i a) j) k
    rw [←hc false false,←hc true false,←hc false true,←hc true true] at he
    exact he
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i k c
    have he := vectorBilinear_equal_bits _ _ _ _ (hfirst k c)
    cases i
    · exact he.1
    · exact he.2
  · intro i k a
    have he := vectorBilinear_equal_bits _ _ _ _ (hlast i a)
    cases k
    · exact he.1
    · exact he.2
  · intro i j k c
    apply Pzero_vanishing_cup
    have he := vectorBilinear_zero _ _ _ _ (hfirst k c)
    cases i <;> cases j
    · exact he.1
    · exact he.2.2.1
    · exact he.2.1
    · exact he.2.2.2
  · intro i j k a
    apply Pzero_vanishing_cup
    have he := vectorBilinear_zero _ _ _ _ (hlast i a)
    cases j <;> cases k
    · exact he.1
    · exact he.2.2.1
    · exact he.2.1
    · exact he.2.2.2
  · intro i a
    exact vectorBilinear_bitSwap _ _ _ _ (hlast i a)

theorem trilinear_rigidity (f : TripleSpectral)
    (hx : ∀ y z a b c, AffineFunction (fun x => f x y z a b c))
    (hy : ∀ x z a b c, AffineFunction (fun y => f x y z a b c))
    (hz : ∀ x y a b c, AffineFunction (fun z => f x y z a b c))
    (hp1 : ∀ a b c, a=Spin.plus → ∀ x y z, f x y z a b c=f 0 y z a b c)
    (hp2 : ∀ a b c, b=Spin.plus → ∀ x y z, f x y z a b c=f x 0 z a b c)
    (hp3 : ∀ a b c, c=Spin.plus → ∀ x y z, f x y z a b c=f x y 0 a b c)
    (hm1 : ∀ a b c, a=Spin.minus → ∀ y z, f 0 y z a b c=0)
    (hm2 : ∀ a b c, b=Spin.minus → ∀ x z, f x 0 z a b c=0)
    (hm3 : ∀ a b c, c=Spin.minus → ∀ x y, f x y 0 a b c=0)
    (hex1 : ∀ z c, PairFunctionExchange (fun x y ab => f x y z ab.1 ab.2 c))
    (hex2 : ∀ x a, PairFunctionExchange (fun y z bc => f x y z a bc.1 bc.2)) :
    ∀ x y z a b c, f x y z a b c=0 := by
  have he := bit_tensor_rigidity (spectralBits f)
    ⟨spectralBits_support f hp1 hp2 hp3 hm1 hm2 hm3,
      spectralBits_channels f hx hy hz hex1 hex2⟩
  intro x y z a b c
  apply triaffine_zero (fun x y z => f x y z a b c)
    (fun y z => hx y z a b c) (fun x z => hy x z a b c) (fun x y => hz x y a b c)
    (fun i j k => ?_) x y z
  exact congrFun (congrFun (congrFun (congrFun (congrFun (congrFun he i) j) k) a) b) c

end PolynomialVacuumAlgebra

end OAI
