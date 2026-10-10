import OAI.Analysis.Naimark.HNN
import OAI.Analysis.Naimark.DirectLimit

namespace OAI

noncomputable section

namespace NaimarkZFC

open scoped CStarAlgebra ComplexOrder OnePoint
namespace PeakingPairData
variable {A C : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  (B : PeakingPairData A) (D : PeakingPairData C) (ι : A →⋆ₐ[ℂ] C)
  (hp : ∀ i n, ι (B.peak i n) = D.peak i n) (F : C →L[ℂ] A)
  (hfix : ∀ a, F (ι a) = a)
  (hstate : ∀ f : A →L[ℂ] ℂ, IsState f → IsState (f.comp F))
  (hleft : ∀ a x, F (ι a*x) = a*F x) (hright : ∀ x a, F (x*ι a) = F x*a)
  (ht : ∀ x, B.trace (F x) = D.trace x)

include hp hfix hstate in
theorem state_composite (i : Bool) (x : C) : D.state i x = B.state i (F x) := by
  have hh := (D.peaks i).2.2.2.2 ((B.state i).comp F) (hstate _ (B.peaks i).2.2.1) (fun n => by
    change B.state i (F (D.peak i n)) = 1
    rw [← hp,hfix]
    exact (B.peaks i).2.2.2.1 n)
  exact (congrArg (fun g : C →L[ℂ] ℂ => g x) hh).symm

include hp hfix hstate hleft hright ht in

theorem expectation_composite (i : Bool) (x : C) :
    (D.input false).expectation i x = (B.input false).expectation i (F x) := by
  ext z
  induction z using OnePoint.rec with
  | infty =>
    rw [D.expectation_infty,B.expectation_infty]
    exact B.state_composite D ι hp F hfix hstate i x
  | coe n =>
    rw [D.expectation_nat,B.expectation_nat,← B.atom_natural D ι hp i n,
      ← ht,← ht,hright,hleft,hfix]

include hp hfix hstate hleft hright ht in

theorem turnCentered_of_expectation_zero (x : C) (hx : F x = 0)
    (i : Bool) (a b : A) : D.turnCentered i (ι a*x*ι b) := by
  change (D.input false).expectation (!i) (ι a*x*ι b) = 0
  rw [B.expectation_composite D ι hp F hfix hstate hleft hright ht,hright,hleft,hx,mul_zero,zero_mul,map_zero]

end PeakingPairData

open Topology
section
variable {A B C : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]
  (φ : A →⋆ₐ[ℂ] B) (ψ : B →⋆ₐ[ℂ] C) (v : Bool → C)
  (K : Bool → A → Prop) (L : Bool → B → Prop)

theorem hnnReducedSpan_le_baseTailSpan (hKL : ∀ i a, K i a → L i (φ a)) :
    hnnReducedSpan (ψ.comp φ) v K ≤ hnnBaseTailSpan φ ψ v L := by
  apply Submodule.span_le.mpr
  rintro x ⟨w,a,hw,rfl⟩
  exact hnnBaseTailSpan_contains_word φ ψ v K L hKL w a hw

theorem hnnBaseTailSpan_mul_center_span
    (hKL : ∀ i a, K i a → L i (φ a))
    (b : B) (hb : ∀ i a c, L i (φ a*b*φ c))
    {x z : C} (hx : x ∈ hnnBaseTailSpan φ ψ v L)
    (hz : z ∈ hnnReducedSpan (ψ.comp φ) v K) :
    x*ψ b*z ∈ hnnBaseTailSpan φ ψ v L := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨w,a,hw,rfl⟩ := hz
    exact hnnBaseTailSpan_mul_center_word φ ψ v K L hKL b hb w a hw hx
  | zero => simpa only [mul_zero] using (hnnBaseTailSpan φ ψ v L).zero_mem
  | add z t hz ht iz it =>
    simpa only [mul_add] using (hnnBaseTailSpan φ ψ v L).add_mem iz it
  | smul c z hz iz =>
    simpa only [mul_smul_comm] using (hnnBaseTailSpan φ ψ v L).smul_mem c iz

theorem hnnBaseTailClosure_mul_center_closure
    (hKL : ∀ i a, K i a → L i (φ a))
    (b : B) (hb : ∀ i a c, L i (φ a*b*φ c))
    {x z : C} (hx : x ∈ closure (hnnBaseTailSpan φ ψ v L : Set C))
    (hz : z ∈ closure (hnnReducedSpan (ψ.comp φ) v K : Set C)) :
    x*ψ b*z ∈ closure (hnnBaseTailSpan φ ψ v L : Set C) := by
  have hfirst : ∀ y ∈ hnnBaseTailSpan φ ψ v L,
      y*ψ b*z ∈ closure (hnnBaseTailSpan φ ψ v L : Set C) := by
    intro y hy
    apply closure_minimal (s := (hnnReducedSpan (ψ.comp φ) v K : Set C))
      (t := (fun z => y*ψ b*z) ⁻¹' closure (hnnBaseTailSpan φ ψ v L : Set C)) _
      (isClosed_closure.preimage (continuous_const.mul continuous_id)) hz
    intro t ht
    exact subset_closure (hnnBaseTailSpan_mul_center_span φ ψ v K L hKL b hb hy ht)
  exact closure_minimal hfirst (isClosed_closure.preimage
    ((continuous_id.mul continuous_const).mul continuous_const)) hx

theorem hnnBaseTailClosure_expectation_zero (E : C →L[ℂ] B)
    (hred : ∀ (w : HNNWord B) (b : B), w.Reduced L → E (ψ b*w.eval ψ v) = 0)
    {x : C} (hx : x ∈ closure (hnnBaseTailSpan φ ψ v L : Set C)) : E x = 0 := by
  apply closure_minimal (s := (hnnBaseTailSpan φ ψ v L : Set C))
    (t := {z | E z = 0}) _ (isClosed_eq E.continuous continuous_const) hx
  intro z hz
  induction hz using Submodule.span_induction with
  | mem z hz => obtain ⟨w,b,hw,_,rfl⟩ := hz; exact hred w b hw
  | zero => exact map_zero E
  | add a b ha hb ia ib =>
    change E (a+b) = 0
    rw [map_add,ia,ib,add_zero]
  | smul c a ha ia =>
    change E (c • a) = 0
    rw [map_smul,ia,smul_zero]

def hnnAlternatingSpine (ψ : B →⋆ₐ[ℂ] C) (x : C) : List (B × C) → C
  | [] => x
  | (b,z)::r => hnnAlternatingSpine ψ (x*ψ b*z) r

theorem hnnAlternatingSpine_mem_closure
    (hKL : ∀ i a, K i a → L i (φ a))
    (F : B →L[ℂ] A)
    (hcenter : ∀ b, F b = 0 → ∀ i a c, L i (φ a*b*φ c))
    (x : C) (hx : x ∈ closure (hnnReducedSpan (ψ.comp φ) v K : Set C))
    (r : List (B × C))
    (hr : ∀ p ∈ r, F p.1 = 0 ∧ p.2 ∈ closure (hnnReducedSpan (ψ.comp φ) v K : Set C)) :
    hnnAlternatingSpine ψ x r ∈ closure (hnnBaseTailSpan φ ψ v L : Set C) := by
  have hx' := closure_mono (hnnReducedSpan_le_baseTailSpan φ ψ v K L hKL) hx
  suffices ∀ y ∈ closure (hnnBaseTailSpan φ ψ v L : Set C),
      hnnAlternatingSpine ψ y r ∈ closure (hnnBaseTailSpan φ ψ v L : Set C) from this x hx'
  induction r with
  | nil => intro y hy; exact hy
  | cons p r ih =>
    intro y hy
    apply ih (fun q hq => hr q (List.mem_cons_of_mem p hq))
    exact hnnBaseTailClosure_mul_center_closure φ ψ v K L hKL p.1
      (hcenter p.1 (hr p (List.mem_cons_self)).1) hy (hr p (List.mem_cons_self)).2

theorem hnnAlternatingSpine_expectation_zero
    (hKL : ∀ i a, K i a → L i (φ a))
    (F : B →L[ℂ] A) (E : C →L[ℂ] B)
    (hcenter : ∀ b, F b = 0 → ∀ i a c, L i (φ a*b*φ c))
    (hred : ∀ (w : HNNWord B) (b : B), w.Reduced L → E (ψ b*w.eval ψ v) = 0)
    (hleft : ∀ b z, E (ψ b*z) = b*E z) (hright : ∀ z b, E (z*ψ b) = E z*b)
    (x : C) (hx : x ∈ closure (hnnReducedSpan (ψ.comp φ) v K : Set C))
    (r : List (B × C))
    (hr : ∀ p ∈ r, F p.1 = 0 ∧ p.2 ∈ closure (hnnReducedSpan (ψ.comp φ) v K : Set C))
    (b c : B) : E (ψ b*hnnAlternatingSpine ψ x r*ψ c) = 0 := by
  rw [hright,hleft,hnnBaseTailClosure_expectation_zero φ ψ v L E hred
    (hnnAlternatingSpine_mem_closure φ ψ v K L hKL F hcenter x hx r hr),mul_zero,zero_mul]

end

open Topology
section
variable {A B C : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]
  (φ : A →⋆ₐ[ℂ] B) (ψ : B →⋆ₐ[ℂ] C) (v : Bool → C)
  (K : Bool → A → Prop) (L : Bool → B → Prop)
  (hKL : ∀ i a, K i a → L i (φ a))
  (F : B →L[ℂ] A) (E : C →L[ℂ] B)
  (hcenter : ∀ b, F b = 0 → ∀ i a c, L i (φ a*b*φ c))
  (hred : ∀ (w : HNNWord B) (b : B), w.Reduced L → E (ψ b*w.eval ψ v) = 0)
  (hleft : ∀ b z, E (ψ b*z) = b*E z) (hright : ∀ z b, E (z*ψ b) = E z*b)

def HNNCenteredBlock (i : Bool) (x : C) : Prop :=
  if i then x ∈ closure (hnnReducedSpan (ψ.comp φ) v K : Set C)
  else ∃ b : B, F b = 0 ∧ ψ b = x

include hKL hcenter hred hright in
private theorem hnn_alternating_tail_zero
    (r : List (Bool × C))
    (hr : ∀ p ∈ r, HNNCenteredBlock φ ψ v K F p.1 p.2)
    (hc : r.IsChain (fun p q => p.1 ≠ q.1))
    (hfirst : ∀ p ∈ r.head?, p.1 = false)
    {x : C} (hx : x ∈ closure (hnnBaseTailSpan φ ψ v L : Set C)) :
    E (x*wordValue r) = 0 := by
  induction r using List.twoStepInduction generalizing x with
  | nil =>
    rw [wordValue_nil,mul_one]
    exact hnnBaseTailClosure_expectation_zero φ ψ v L E hred hx
  | singleton p =>
    have hp := hfirst p (by simp)
    have hb := hr p (by simp)
    simp only [HNNCenteredBlock,hp,Bool.false_eq_true,ite_false] at hb
    obtain ⟨b,hb,hbp⟩ := hb
    simp only [wordValue_cons,wordValue_nil,mul_one,← hbp,hright,
      hnnBaseTailClosure_expectation_zero φ ψ v L E hred hx,zero_mul]
  | cons_cons p q r ih _ =>
    have hp := hfirst p (by simp)
    have hq : q.1 = true := by
      have h := hc.rel
      cases hqp : q.1 <;> simp_all
    have hb := hr p (by simp)
    simp only [HNNCenteredBlock,hp,Bool.false_eq_true,ite_false] at hb
    obtain ⟨b,hb,hbp⟩ := hb
    have hz := hr q (by simp)
    simp only [HNNCenteredBlock,hq,ite_true] at hz
    have hnew := hnnBaseTailClosure_mul_center_closure φ ψ v K L hKL b
      (hcenter b hb) hx hz
    have hfirst' : ∀ t ∈ r.head?, t.1 = false := by
      intro t ht
      have h := hc.tail.rel_head? ht
      cases htp : t.1 <;> simp_all
    have ih' := ih (fun t ht => hr t (by simp only [List.mem_cons]; exact Or.inr (Or.inr ht)))
      hc.tail.tail hfirst' hnew
    simpa only [wordValue_cons,← hbp,mul_assoc] using ih'

include hKL hcenter hred hleft hright in

theorem hnn_alternating_expectation_zero
    (hbase : ∀ b, E (ψ b) = b)
    (r : List (Bool × C)) (hne : r ≠ [])
    (hr : ∀ p ∈ r, HNNCenteredBlock φ ψ v K F p.1 p.2)
    (hc : r.IsChain (fun p q => p.1 ≠ q.1)) :
    F (E (wordValue r)) = 0 := by
  cases r with
  | nil => exact (hne rfl).elim
  | cons p r =>
    cases hp : p.1 with
    | true =>
      have hx := hr p (by simp)
      simp only [HNNCenteredBlock,hp,ite_true] at hx
      have hx' := closure_mono (hnnReducedSpan_le_baseTailSpan φ ψ v K L hKL) hx
      have hfirst : ∀ q ∈ r.head?, q.1 = false := by
        intro q hq
        have h := hc.rel_head? hq
        cases heq : q.1 <;> simp_all
      rw [wordValue_cons,hnn_alternating_tail_zero φ ψ v K L hKL F E hcenter hred hright r
        (fun q hq => hr q (by simp only [List.mem_cons]; exact Or.inr hq)) hc.tail hfirst hx',map_zero]
    | false =>
      have hb := hr p (by simp)
      simp only [HNNCenteredBlock,hp,Bool.false_eq_true,ite_false] at hb
      obtain ⟨b,hb,hbp⟩ := hb
      cases r with
      | nil => simpa only [wordValue_cons,wordValue_nil,mul_one,← hbp,hbase] using hb
      | cons q r =>
        have hq : q.1 = true := by
          have h := hc.rel
          cases heq : q.1 <;> simp_all
        have hx := hr q (by simp)
        simp only [HNNCenteredBlock,hq,ite_true] at hx
        have hx' := closure_mono (hnnReducedSpan_le_baseTailSpan φ ψ v K L hKL) hx
        have hfirst : ∀ t ∈ r.head?, t.1 = false := by
          intro t ht
          have h := hc.tail.rel_head? ht
          cases ht' : t.1 <;> simp_all
        have ht := hnn_alternating_tail_zero φ ψ v K L hKL F E hcenter hred hright r
          (fun t ht => hr t (by simp only [List.mem_cons]; exact Or.inr (Or.inr ht)))
          hc.tail.tail hfirst hx'
        rw [wordValue_cons,wordValue_cons,← hbp,hleft,ht,mul_zero,map_zero]

end

open Topology
section
variable {A B C : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]
  (φ : A →⋆ₐ[ℂ] B) (ψ : A →⋆ₐ[ℂ] C) (v : Bool → B) (w : Bool → C)
  (K : Bool → A → Prop) (F : B →⋆ₐ[ℂ] C)
  (hbase : ∀ a, F (φ a) = ψ a) (hletter : ∀ i, F (v i) = w i)

include hbase hletter in
theorem hnnReducedSpan_map {x : B} (hx : x ∈ hnnReducedSpan φ v K) :
    F x ∈ hnnReducedSpan ψ w K := by
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨u,a,hu,rfl⟩ := hz
    rw [map_mul,hbase,HNNWord.eval_hom φ ψ v w F hbase hletter]
    exact Submodule.subset_span ⟨u,a,hu,rfl⟩
  | zero => simpa only [map_zero] using (hnnReducedSpan ψ w K).zero_mem
  | add x y hx hy ix iy => simpa only [map_add] using (hnnReducedSpan ψ w K).add_mem ix iy
  | smul c x hx ix => simpa only [map_smul] using (hnnReducedSpan ψ w K).smul_mem c ix

include hbase hletter in
theorem hnnReducedClosure_map {x : B} (hx : x ∈ closure (hnnReducedSpan φ v K : Set B)) :
    F x ∈ closure (hnnReducedSpan ψ w K : Set C) := by
  have hs : (hnnReducedSpan φ v K : Set B) ⊆
      F ⁻¹' closure (hnnReducedSpan ψ w K : Set C) :=
    fun z hz => subset_closure (hnnReducedSpan_map φ ψ v w K F hbase hletter hz)
  have hc : IsClosed (F ⁻¹' closure (hnnReducedSpan ψ w K : Set C)) :=
    isClosed_closure.preimage (starAlgHomCLM F).continuous
  exact closure_minimal hs hc hx

end

open Topology
open scoped CStarAlgebra ComplexOrder
namespace PeakingPairData
variable {A C : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  (B : PeakingPairData A) (D : PeakingPairData C)

theorem hnn_kernel_reduced {x : B.HNNAlgebra} (hx : B.hnnExpectation x = 0) :
    x ∈ closure (hnnReducedSpan B.hnnBase B.hnnLetter B.turnCentered : Set B.HNNAlgebra) :=
  hnn_kernel_mem_closure_reducedSpan B.hnnBase B.hnnLetter B.turnCentered
    B.hnnExpectation B.hnnExpectation_base B.hnnExpectation_word
    (hnnWordSpan_dense B.hnnBase B.hnnLetter B.turnCentered B.hnnLetter_star
      B.turnCenter B.turnRemainder B.turnCenter_centered B.hnnLetter_turn B.hnn_generated) hx

theorem hnnExpectation_state (f : A →L[ℂ] ℂ) (hf : IsState f) :
    IsState (f.comp B.hnnExpectation) := B.expectCorner_state f hf

variable (ι : A →⋆ₐ[ℂ] C) (hp : ∀ i n, ι (B.peak i n) = D.peak i n)
  (F : C →L[ℂ] A) (hfix : ∀ a, F (ι a) = a)
  (hstate : ∀ f : A →L[ℂ] ℂ, IsState f → IsState (f.comp F))
  (hleft : ∀ a x, F (ι a*x) = a*F x) (hright : ∀ x a, F (x*ι a) = F x*a)
  (ht : ∀ x, B.trace (F x) = D.trace x)
  (J : B.HNNAlgebra →⋆ₐ[ℂ] D.HNNAlgebra)
  (hJa : ∀ a, J (B.hnnBase a) = D.hnnBase (ι a))
  (hJv : ∀ i, J (B.hnnLetter i) = D.hnnLetter i)

include hJa hJv in
theorem hnn_mapped_kernel {x : B.HNNAlgebra} (hx : B.hnnExpectation x = 0) :
    J x ∈ closure (hnnReducedSpan (D.hnnBase.comp ι) D.hnnLetter B.turnCentered : Set D.HNNAlgebra) :=
  hnnReducedClosure_map B.hnnBase (D.hnnBase.comp ι) B.hnnLetter D.hnnLetter
    B.turnCentered J hJa hJv (B.hnn_kernel_reduced hx)

include hp hfix hstate hleft hright ht in

theorem hnn_free_blocks (r : List (Bool × D.HNNAlgebra)) (hne : r ≠ [])
    (hr : ∀ p ∈ r, HNNCenteredBlock ι D.hnnBase D.hnnLetter B.turnCentered F p.1 p.2)
    (hc : r.IsChain (fun p q => p.1 ≠ q.1)) :
    F (D.hnnExpectation (wordValue r)) = 0 := by
  have htrace (a : A) : D.trace (ι a) = B.trace a := by rw [← ht,hfix]
  have hKL (i : Bool) (a : A) (ha : B.turnCentered i a) : D.turnCentered i (ι a) := by
    change (D.input false).expectation (!i) (ι a) = 0
    rw [B.expectation_natural D ι hp htrace]
    exact ha
  exact hnn_alternating_expectation_zero ι D.hnnBase D.hnnLetter B.turnCentered D.turnCentered
    hKL F D.hnnExpectation
    (fun x hx i a b => B.turnCentered_of_expectation_zero D ι hp F hfix hstate
      hleft hright ht x hx i a b)
    D.hnnExpectation_word D.hnnExpectation_left D.hnnExpectation_right
    D.hnnExpectation_base r hne hr hc

end PeakingPairData

section
variable {I R : Type*} [Ring R] [Algebra ℂ R]

theorem CenteredDecomposition.moments_agree
    {D : NonUnitalSubalgebra ℂ R} {X : I → NonUnitalSubalgebra ℂ R}
    {K : I → Submodule ℂ R} (h : CenteredDecomposition D X K)
    (f g : R →ₗ[ℂ] ℂ) (hD : ∀ d ∈ D, f d = g d)
    (hf : ∀ w, IsCenteredWord K w → w ≠ [] → f (wordValue w) = 0)
    (hg : ∀ w, IsCenteredWord K w → w ≠ [] → g (wordValue w) = 0)
    (h1 : f 1 = g 1) {r : R}
    (hr : r ∈ Algebra.adjoin ℂ (⋃ i, (X i : Set R))) : f r = g r := by
  have hn := h.adjoin_le_normalSpan hr
  clear hr
  induction hn using Submodule.span_induction with
  | mem r hr =>
    rcases hr with hr | ⟨w,hw,rfl⟩
    · exact hD r hr
    · by_cases he : w = []
      · simpa [he] using h1
      · rw [hf w hw he,hg w hw he]
  | zero => simp
  | add a b _ _ ha hb => simp only [map_add,ha,hb]
  | smul c a _ ha => simp only [map_smul,ha]

variable {A B C : Type*} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B]
  [Ring C] [Algebra ℂ C] (V : I → Type*) [∀ i, Ring (V i)] [∀ i, Algebra ℂ (V i)]
  (inc : ∀ i, A →ₐ[ℂ] V i) (E : ∀ i, V i →ₗ[ℂ] A)
  (φ : ∀ i, V i →ₐ[ℂ] B) (ψ : ∀ i, V i →ₐ[ℂ] C)
  (b : A →ₐ[ℂ] B) (c : A →ₐ[ℂ] C)

def pairedDiagonal : NonUnitalSubalgebra ℂ (B × C) :=
  (b.prod c).range.toNonUnitalSubalgebra

def pairedFactors : I → NonUnitalSubalgebra ℂ (B × C) :=
  fun i => ((φ i).prod (ψ i)).range.toNonUnitalSubalgebra

def pairedCenters : I → Submodule ℂ (B × C) :=
  fun i => (LinearMap.ker (E i)).map ((φ i).prod (ψ i)).toLinearMap

theorem paired_centered_decomposition
    (hb : ∀ i, (φ i).comp (inc i) = b) (hc : ∀ i, (ψ i).comp (inc i) = c)
    (hfix : ∀ i a, E i (inc i a) = a)
    (hmod : ∀ i a x, E i (inc i a*x) = a*E i x) :
    CenteredDecomposition (pairedDiagonal b c) (pairedFactors V φ ψ)
      (pairedCenters V E φ ψ) := by
  have hp (i : I) (a : A) : ((φ i).prod (ψ i)) (inc i a) = (b.prod c) a := by
    apply Prod.ext
    · exact congrArg (fun h : A →ₐ[ℂ] B => h a) (hb i)
    · exact congrArg (fun h : A →ₐ[ℂ] C => h a) (hc i)
  constructor
  · intro i d hd
    obtain ⟨a,rfl⟩ := hd
    exact ⟨inc i a,hp i a⟩
  · intro i x hx
    obtain ⟨a,_,ha⟩ := hx
    exact ⟨a,ha⟩
  · intro i x hx
    obtain ⟨a,rfl⟩ := hx
    refine ⟨(b.prod c) (E i a),⟨E i a,rfl⟩,
      ((φ i).prod (ψ i)) (a-inc i (E i a)),?_,?_⟩
    · exact ⟨a-inc i (E i a),by
        change E i (a-inc i (E i a)) = 0
        rw [map_sub,hfix,sub_self],rfl⟩
    · rw [map_sub,hp,add_sub_cancel]
      rfl
  · intro i d x hd hx
    obtain ⟨a,rfl⟩ := hd
    obtain ⟨t,ht,rfl⟩ := hx
    refine ⟨inc i a*t,?_,?_⟩
    · change E i (inc i a*t) = 0
      rw [hmod,show E i t = 0 from ht,mul_zero]
    · change ((φ i).prod (ψ i)) (inc i a*t) = _
      rw [map_mul,hp]
      rfl

end

section
variable {I R S : Type*} [Ring R] [Algebra ℂ R] [Ring S] [Algebra ℂ S]

theorem IsCenteredWord.map_algHom {K : I → Submodule ℂ R}
    {L : I → Submodule ℂ S} (φ : R →ₐ[ℂ] S)
    (hKL : ∀ i a, a ∈ K i → φ a ∈ L i)
    {w : List (I × R)} (hw : IsCenteredWord K w) :
    IsCenteredWord L (w.map (fun p => (p.1,φ p.2))) := by
  refine ⟨?_,(List.isChain_map _).mpr hw.alternating⟩
  intro p hp
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  exact hKL q.1 q.2 (hw.centered q hq)

@[simp] theorem wordValue_map_algHom (φ : R →ₐ[ℂ] S) (w : List (I × R)) :
    wordValue (w.map (fun p => (p.1,φ p.2))) = φ (wordValue w) := by
  induction w with
  | nil => simp
  | cons p w ih => simp only [List.map_cons,wordValue_cons,map_mul,ih]

variable {A B C : Type*} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B]
  [Ring C] [Algebra ℂ C] (V : I → Type*) [∀ i, Ring (V i)] [∀ i, Algebra ℂ (V i)]
  (inc : ∀ i, A →ₐ[ℂ] V i) (E : ∀ i, V i →ₗ[ℂ] A)
  (φ : ∀ i, V i →ₐ[ℂ] B) (ψ : ∀ i, V i →ₐ[ℂ] C)
  (b : A →ₐ[ℂ] B) (c : A →ₐ[ℂ] C)

def factorCenters : I → Submodule ℂ B :=
  fun i => (LinearMap.ker (E i)).map (φ i).toLinearMap

theorem paired_free_moments_equal
    (hb : ∀ i, (φ i).comp (inc i) = b) (hc : ∀ i, (ψ i).comp (inc i) = c)
    (hfix : ∀ i a, E i (inc i a) = a)
    (hmod : ∀ i a x, E i (inc i a*x) = a*E i x)
    (f : B →ₗ[ℂ] ℂ) (g : C →ₗ[ℂ] ℂ)
    (hbase : ∀ a, f (b a) = g (c a))
    (hf : ∀ w, IsCenteredWord (factorCenters V E φ) w → w ≠ [] →
      f (wordValue w) = 0)
    (hg : ∀ w, IsCenteredWord (factorCenters V E ψ) w → w ≠ [] →
      g (wordValue w) = 0)
    {z : B × C} (hz : z ∈ Algebra.adjoin ℂ (⋃ i, (pairedFactors V φ ψ i : Set (B × C)))) :
    f z.1 = g z.2 := by
  let p : B × C →ₐ[ℂ] B := AlgHom.fst ℂ B C
  let q : B × C →ₐ[ℂ] C := AlgHom.snd ℂ B C
  have hp : ∀ i x, x ∈ pairedCenters V E φ ψ i → p x ∈ factorCenters V E φ i := by
    intro i x hx
    obtain ⟨a,ha,rfl⟩ := hx
    exact ⟨a,ha,rfl⟩
  have hq : ∀ i x, x ∈ pairedCenters V E φ ψ i → q x ∈ factorCenters V E ψ i := by
    intro i x hx
    obtain ⟨a,ha,rfl⟩ := hx
    exact ⟨a,ha,rfl⟩
  apply (paired_centered_decomposition V inc E φ ψ b c hb hc hfix hmod).moments_agree
    (f.comp p.toLinearMap) (g.comp q.toLinearMap) ?_ ?_ ?_ ?_ hz
  · intro d hd
    obtain ⟨a,rfl⟩ := hd
    exact hbase a
  · intro w hw hne
    have h := hf _ (hw.map_algHom p hp) (by simpa using hne)
    simpa only [wordValue_map_algHom,LinearMap.comp_apply,AlgHom.toLinearMap_apply] using h
  · intro w hw hne
    have h := hg _ (hw.map_algHom q hq) (by simpa using hne)
    simpa only [wordValue_map_algHom,LinearMap.comp_apply,AlgHom.toLinearMap_apply] using h
  · simpa using hbase 1
end

open Topology
open scoped ComplexOrder
section
variable {I A B C : Type*} [Ring A] [Algebra ℂ A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  (V : I → Type*) [∀ i, Ring (V i)] [∀ i, StarRing (V i)] [∀ i, Algebra ℂ (V i)]
  (φ : ∀ i, V i →⋆ₐ[ℂ] B) (ψ : ∀ i, V i →⋆ₐ[ℂ] C)

def jointStarModel : StarSubalgebra ℂ (B × C) :=
  StarAlgebra.adjoin ℂ (⋃ i, Set.range ((φ i).prod (ψ i)))

def jointFirst : jointStarModel V φ ψ →⋆ₐ[ℂ] B :=
  (StarAlgHom.fst ℂ B C).comp (jointStarModel V φ ψ).subtype

def jointSecond : jointStarModel V φ ψ →⋆ₐ[ℂ] C :=
  (StarAlgHom.snd ℂ B C).comp (jointStarModel V φ ψ).subtype

omit [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C] in
theorem jointFirst_dense
    (hd : Dense (StarAlgebra.adjoin ℂ (⋃ i, Set.range (φ i)) : Set B)) :
    DenseRange (jointFirst V φ ψ) := by
  apply hd.mono
  intro x hx
  apply StarAlgebra.adjoin_le (S := (jointFirst V φ ψ).range) ?_ hx
  intro y hy
  obtain ⟨i,a,rfl⟩ := Set.mem_iUnion.mp hy
  refine ⟨⟨((φ i).prod (ψ i)) a,StarAlgebra.subset_adjoin ℂ _ ?_⟩,rfl⟩
  exact Set.mem_iUnion.mpr ⟨i,a,rfl⟩

omit [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C] in
theorem jointSecond_dense
    (hd : Dense (StarAlgebra.adjoin ℂ (⋃ i, Set.range (ψ i)) : Set C)) :
    DenseRange (jointSecond V φ ψ) := by
  apply hd.mono
  intro x hx
  apply StarAlgebra.adjoin_le (S := (jointSecond V φ ψ).range) ?_ hx
  intro y hy
  obtain ⟨i,a,rfl⟩ := Set.mem_iUnion.mp hy
  refine ⟨⟨((φ i).prod (ψ i)) a,StarAlgebra.subset_adjoin ℂ _ ?_⟩,rfl⟩
  exact Set.mem_iUnion.mpr ⟨i,a,rfl⟩

variable (inc : ∀ i, A →ₐ[ℂ] V i) (E : ∀ i, V i →ₗ[ℂ] A)
  (b : A →ₐ[ℂ] B) (c : A →ₐ[ℂ] C)
  (hb : ∀ i, (φ i).toAlgHom.comp (inc i) = b)
  (hc : ∀ i, (ψ i).toAlgHom.comp (inc i) = c)
  (hfix : ∀ i a, E i (inc i a) = a)
  (hmod : ∀ i a x, E i (inc i a*x) = a*E i x)
  (f : B →ₚ[ℂ] ℂ) (g : C →ₚ[ℂ] ℂ)
  (hbase : ∀ a, f (b a) = g (c a))
  (hfreeB : ∀ w, IsCenteredWord (factorCenters V E (fun i => (φ i).toAlgHom)) w →
    w ≠ [] → f (wordValue w) = 0)
  (hfreeC : ∀ w, IsCenteredWord (factorCenters V E (fun i => (ψ i).toAlgHom)) w →
    w ≠ [] → g (wordValue w) = 0)
include hb hc hfix hmod hbase hfreeB hfreeC

omit [StarOrderedRing B] [StarOrderedRing C] in
theorem jointStarModel_moments (z : jointStarModel V φ ψ) :
    f (jointFirst V φ ψ z) = g (jointSecond V φ ψ z) := by
  apply paired_free_moments_equal V inc E (fun i => (φ i).toAlgHom)
    (fun i => (ψ i).toAlgHom) b c hb hc hfix hmod f.toLinearMap g.toLinearMap
    hbase hfreeB hfreeC
  have hs : star (⋃ i, Set.range ((φ i).prod (ψ i))) ⊆
      ⋃ i, Set.range ((φ i).prod (ψ i)) := by
    intro x hx
    obtain ⟨i,a,ha⟩ := Set.mem_iUnion.mp (Set.mem_star.mp hx)
    exact Set.mem_iUnion.mpr ⟨i,star a,by rw [map_star,ha,star_star]⟩
  have hz := z.property
  change (z : B × C) ∈ (StarAlgebra.adjoin ℂ
    (⋃ i, Set.range ((φ i).prod (ψ i)))).toSubalgebra at hz
  rw [StarAlgebra.adjoin_toSubalgebra,Set.union_eq_self_of_subset_right hs] at hz
  exact hz

def jointFreeEquiv
    (hdB : Dense (StarAlgebra.adjoin ℂ (⋃ i, Set.range (φ i)) : Set B))
    (hdC : Dense (StarAlgebra.adjoin ℂ (⋃ i, Set.range (ψ i)) : Set C))
    (hf : ∀ x : B, f (star x*x) = 0 → x = 0)
    (hg : ∀ x : C, g (star x*x) = 0 → x = 0) : B ≃⋆ₐ[ℂ] C :=
  starAlgEquivOfFaithfulMoments (jointFirst V φ ψ) (jointSecond V φ ψ)
    (jointFirst_dense V φ ψ hdB) (jointSecond_dense V φ ψ hdC) f g
    (jointStarModel_moments V φ ψ inc E b c hb hc hfix hmod f g hbase hfreeB hfreeC) hf hg

variable (hdB : Dense (StarAlgebra.adjoin ℂ (⋃ i, Set.range (φ i)) : Set B))
    (hdC : Dense (StarAlgebra.adjoin ℂ (⋃ i, Set.range (ψ i)) : Set C))
    (hf : ∀ x : B, f (star x*x) = 0 → x = 0)
    (hg : ∀ x : C, g (star x*x) = 0 → x = 0)

@[simp] theorem jointFreeEquiv_factor (i : I) (a : V i) :
    jointFreeEquiv V φ ψ inc E b c hb hc hfix hmod f g hbase hfreeB hfreeC hdB hdC hf hg
      (φ i a) = ψ i a := by
  let z : jointStarModel V φ ψ := ⟨((φ i).prod (ψ i)) a,
    StarAlgebra.subset_adjoin ℂ _ (Set.mem_iUnion.mpr ⟨i,a,rfl⟩)⟩
  exact starAlgEquivOfFaithfulMoments_apply (jointFirst V φ ψ) (jointSecond V φ ψ)
    (jointFirst_dense V φ ψ hdB) (jointSecond_dense V φ ψ hdC) f g
    (jointStarModel_moments V φ ψ inc E b c hb hc hfix hmod f g hbase hfreeB hfreeC) hf hg z

theorem jointFreeEquiv_preserves (a : B) :
    g (jointFreeEquiv V φ ψ inc E b c hb hc hfix hmod f g hbase hfreeB hfreeC hdB hdC hf hg a) = f a :=
  starAlgEquivOfFaithfulMoments_preserves (jointFirst V φ ψ) (jointSecond V φ ψ)
    (jointFirst_dense V φ ψ hdB) (jointSecond_dense V φ ψ hdC) f g
    (jointStarModel_moments V φ ψ inc E b c hb hc hfix hmod f g hbase hfreeB hfreeC) hf hg a

end

open Topology
open scoped CStarAlgebra ComplexOrder

theorem wordValue_reindex {I J R : Type*} [Ring R] (s : I → J) (w : List (I × R)) :
    wordValue (w.map (fun p => (s p.1,p.2))) = wordValue w := by
  induction w with
  | nil => rfl
  | cons p w ih => simpa only [List.map_cons,wordValue_cons] using congrArg (p.2 * ·) ih

namespace PeakingPairData
variable {A C : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  (B : PeakingPairData A) (D : PeakingPairData C)
  (ι : A →⋆ₐ[ℂ] C) (hp : ∀ i n, ι (B.peak i n) = D.peak i n)
  (F : C →L[ℂ] A) (hfix : ∀ a, F (ι a) = a)
  (hstate : ∀ f : A →L[ℂ] ℂ, IsState f → IsState (f.comp F))
  (hleft : ∀ a x, F (ι a*x) = a*F x) (hright : ∀ x a, F (x*ι a) = F x*a)
  (ht : ∀ x, B.trace (F x) = D.trace x)
  (V : Bool → Type*) [∀ i, Ring (V i)] [∀ i, Algebra ℂ (V i)]
  (E : ∀ i, V i →ₗ[ℂ] A) (φ : ∀ i, V i →ₐ[ℂ] D.HNNAlgebra)

include hp hfix hstate hleft hright ht in

theorem hnn_family_free (s : Bool → Bool) (hs : Function.Injective s)
    (hk : ∀ i x, E i x = 0 →
      HNNCenteredBlock ι D.hnnBase D.hnnLetter B.turnCentered F (s i) (φ i x))
    (w : List (Bool × D.HNNAlgebra)) (hw : IsCenteredWord (factorCenters V E φ) w)
    (hne : w ≠ []) : D.hnnTrace (wordValue w) = 0 := by
  have h := B.hnn_free_blocks D ι hp F hfix hstate hleft hright ht
    (w.map (fun p => (s p.1,p.2))) (by simpa using hne) ?_ ?_
  · rw [wordValue_reindex] at h
    rw [← D.hnnTrace_expectation,← ht,h,map_zero]
  · intro p hpw
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hpw
    obtain ⟨x,hx,hxq⟩ := hw.centered q hq
    change E q.1 x = 0 at hx
    exact hxq ▸ hk q.1 x hx
  · apply (List.isChain_map _).mpr
    exact hw.alternating.imp (fun _ _ h he => h (hs he))

theorem hnn_two_factors_dense (J : B.HNNAlgebra →⋆ₐ[ℂ] D.HNNAlgebra)
    (hv : ∀ i, J (B.hnnLetter i) = D.hnnLetter i)
    (V : Bool → Type*) [∀ i, Ring (V i)] [∀ i, StarRing (V i)] [∀ i, Algebra ℂ (V i)]
    (φ : ∀ i, V i →⋆ₐ[ℂ] D.HNNAlgebra)
    (hb : Set.range D.hnnBase ⊆ ⋃ i, Set.range (φ i))
    (hj : Set.range J ⊆ ⋃ i, Set.range (φ i)) :
    Dense (StarAlgebra.adjoin ℂ (⋃ i, Set.range (φ i)) : Set D.HNNAlgebra) := by
  apply D.hnn_generated.mono
  apply StarAlgebra.adjoin_mono
  intro x hx
  rcases hx with hx | ⟨i,rfl⟩
  · exact hb hx
  · exact hj ⟨B.hnnLetter i,hv i⟩

end PeakingPairData

open Topology
open scoped CStarAlgebra ComplexOrder
namespace PeakingPairData
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (B Q : PeakingPairData A)

def pairHNN : Bool → Type := fun i => if i then Q.HNNAlgebra else B.HNNAlgebra
instance pairHNN_cstar (i : Bool) : CStarAlgebra (pairHNN B Q i) := by
  cases i <;> dsimp [pairHNN] <;> infer_instance

def pairHNNBase : ∀ i, A →⋆ₐ[ℂ] pairHNN B Q i
  | false => B.hnnBase
  | true => Q.hnnBase

def pairHNNExpect : ∀ i, pairHNN B Q i →ₗ[ℂ] A
  | false => B.hnnExpectation.toLinearMap
  | true => Q.hnnExpectation.toLinearMap

theorem pairHNNExpect_fix (i : Bool) (a : A) :
    pairHNNExpect B Q i (pairHNNBase B Q i a) = a := by
  cases i
  · exact B.hnnExpectation_base a
  · exact Q.hnnExpectation_base a

theorem pairHNNExpect_left (i : Bool) (a : A) (x : pairHNN B Q i) :
    pairHNNExpect B Q i (pairHNNBase B Q i a*x) = a*pairHNNExpect B Q i x := by
  cases i
  · exact B.hnnExpectation_left a x
  · exact Q.hnnExpectation_left a x

variable (D : PeakingPairData B.HNNAlgebra) (E : PeakingPairData Q.HNNAlgebra)
  (jQ : Q.HNNAlgebra →⋆ₐ[ℂ] D.HNNAlgebra) (jB : B.HNNAlgebra →⋆ₐ[ℂ] E.HNNAlgebra)

def leftHNNFamily : ∀ i, pairHNN B Q i →⋆ₐ[ℂ] D.HNNAlgebra
  | false => D.hnnBase
  | true => jQ

def rightHNNFamily : ∀ i, pairHNN B Q i →⋆ₐ[ℂ] E.HNNAlgebra
  | false => jB
  | true => E.hnnBase

theorem leftHNNFamily_base (ha : ∀ a, jQ (Q.hnnBase a) = D.hnnBase (B.hnnBase a)) (i : Bool) :
    (leftHNNFamily B Q D jQ i).toAlgHom.comp (pairHNNBase B Q i).toAlgHom =
      (D.hnnBase.comp B.hnnBase).toAlgHom := by
  cases i
  · rfl
  · ext a; exact ha a

theorem rightHNNFamily_base (ha : ∀ a, jB (B.hnnBase a) = E.hnnBase (Q.hnnBase a)) (i : Bool) :
    (rightHNNFamily B Q E jB i).toAlgHom.comp (pairHNNBase B Q i).toAlgHom =
      (E.hnnBase.comp Q.hnnBase).toAlgHom := by
  cases i
  · ext a; exact ha a
  · rfl

theorem leftHNNFamily_free
    (hp : ∀ i n, B.hnnBase (Q.peak i n) = D.peak i n)
    (ht : ∀ x, Q.trace (B.hnnExpectation x) = D.trace x)
    (ha : ∀ a, jQ (Q.hnnBase a) = D.hnnBase (B.hnnBase a))
    (hv : ∀ i, jQ (Q.hnnLetter i) = D.hnnLetter i)
    (w) (hw : IsCenteredWord (factorCenters (pairHNN B Q) (pairHNNExpect B Q)
      (fun i => (leftHNNFamily B Q D jQ i).toAlgHom)) w) (hne : w ≠ []) :
    D.hnnTrace (wordValue w) = 0 := by
  apply Q.hnn_family_free D B.hnnBase hp B.hnnExpectation B.hnnExpectation_base
    B.hnnExpectation_state B.hnnExpectation_left B.hnnExpectation_right ht
    (pairHNN B Q) (pairHNNExpect B Q) (fun i => (leftHNNFamily B Q D jQ i).toAlgHom)
    id Function.injective_id ?_ w hw hne
  intro i x hx
  cases i
  · exact ⟨x,hx,rfl⟩
  · exact Q.hnn_mapped_kernel D B.hnnBase jQ ha hv hx

theorem rightHNNFamily_free
    (hp : ∀ i n, Q.hnnBase (B.peak i n) = E.peak i n)
    (ht : ∀ x, B.trace (Q.hnnExpectation x) = E.trace x)
    (ha : ∀ a, jB (B.hnnBase a) = E.hnnBase (Q.hnnBase a))
    (hv : ∀ i, jB (B.hnnLetter i) = E.hnnLetter i)
    (w) (hw : IsCenteredWord (factorCenters (pairHNN B Q) (pairHNNExpect B Q)
      (fun i => (rightHNNFamily B Q E jB i).toAlgHom)) w) (hne : w ≠ []) :
    E.hnnTrace (wordValue w) = 0 := by
  apply B.hnn_family_free E Q.hnnBase hp Q.hnnExpectation Q.hnnExpectation_base
    Q.hnnExpectation_state Q.hnnExpectation_left Q.hnnExpectation_right ht
    (pairHNN B Q) (pairHNNExpect B Q) (fun i => (rightHNNFamily B Q E jB i).toAlgHom)
    Bool.not Bool.not_injective ?_ w hw hne
  intro i x hx
  cases i
  · exact B.hnn_mapped_kernel E Q.hnnBase jB ha hv hx
  · exact ⟨x,hx,rfl⟩

theorem leftHNNFamily_dense (hv : ∀ i, jQ (Q.hnnLetter i) = D.hnnLetter i) :
    Dense (StarAlgebra.adjoin ℂ (⋃ i, Set.range (leftHNNFamily B Q D jQ i)) : Set D.HNNAlgebra) := by
  apply Q.hnn_two_factors_dense D jQ hv (pairHNN B Q) (leftHNNFamily B Q D jQ)
  · rintro _ ⟨x,rfl⟩; exact Set.mem_iUnion.mpr ⟨false,x,rfl⟩
  · rintro _ ⟨x,rfl⟩; exact Set.mem_iUnion.mpr ⟨true,x,rfl⟩

theorem rightHNNFamily_dense (hv : ∀ i, jB (B.hnnLetter i) = E.hnnLetter i) :
    Dense (StarAlgebra.adjoin ℂ (⋃ i, Set.range (rightHNNFamily B Q E jB i)) : Set E.HNNAlgebra) := by
  apply B.hnn_two_factors_dense E jB hv (pairHNN B Q) (rightHNNFamily B Q E jB)
  · rintro _ ⟨x,rfl⟩; exact Set.mem_iUnion.mpr ⟨true,x,rfl⟩
  · rintro _ ⟨x,rfl⟩; exact Set.mem_iUnion.mpr ⟨false,x,rfl⟩

variable (ht : ∀ a, B.trace a = Q.trace a)
  (hpD : ∀ i n, B.hnnBase (Q.peak i n) = D.peak i n)
  (hpE : ∀ i n, Q.hnnBase (B.peak i n) = E.peak i n)
  (htD : ∀ x, Q.trace (B.hnnExpectation x) = D.trace x)
  (htE : ∀ x, B.trace (Q.hnnExpectation x) = E.trace x)
  (haQ : ∀ a, jQ (Q.hnnBase a) = D.hnnBase (B.hnnBase a))
  (hvQ : ∀ i, jQ (Q.hnnLetter i) = D.hnnLetter i)
  (haB : ∀ a, jB (B.hnnBase a) = E.hnnBase (Q.hnnBase a))
  (hvB : ∀ i, jB (B.hnnLetter i) = E.hnnLetter i)

include ht htD htE in
theorem reorder_base_moments (a : A) :
    D.hnnTrace (D.hnnBase (B.hnnBase a)) = E.hnnTrace (E.hnnBase (Q.hnnBase a)) := by
  rw [D.hnnTrace_base,E.hnnTrace_base,← htD,← htE,B.hnnExpectation_base,Q.hnnExpectation_base,ht]

def reorderEquiv : D.HNNAlgebra ≃⋆ₐ[ℂ] E.HNNAlgebra :=
  jointFreeEquiv (pairHNN B Q) (leftHNNFamily B Q D jQ) (rightHNNFamily B Q E jB)
    (fun i => (pairHNNBase B Q i).toAlgHom) (pairHNNExpect B Q)
    (D.hnnBase.comp B.hnnBase).toAlgHom (E.hnnBase.comp Q.hnnBase).toAlgHom
    (leftHNNFamily_base B Q D jQ haQ) (rightHNNFamily_base B Q E jB haB)
    (pairHNNExpect_fix B Q) (pairHNNExpect_left B Q)
    (positiveOfSquares D.hnnTrace D.hnnTrace_isState.2) (positiveOfSquares E.hnnTrace E.hnnTrace_isState.2)
    (reorder_base_moments B Q D E ht htD htE)
    (leftHNNFamily_free B Q D jQ hpD htD haQ hvQ)
    (rightHNNFamily_free B Q E jB hpE htE haB hvB)
    (leftHNNFamily_dense B Q D jQ hvQ) (rightHNNFamily_dense B Q E jB hvB)
    D.hnnTrace_faithful E.hnnTrace_faithful

theorem reorderEquiv_factor (i : Bool) (a : pairHNN B Q i) :
    reorderEquiv B Q D E jQ jB ht hpD hpE htD htE haQ hvQ haB hvB
      (leftHNNFamily B Q D jQ i a) = rightHNNFamily B Q E jB i a :=
  jointFreeEquiv_factor (pairHNN B Q) (leftHNNFamily B Q D jQ) (rightHNNFamily B Q E jB)
    (fun i => (pairHNNBase B Q i).toAlgHom) (pairHNNExpect B Q)
    (D.hnnBase.comp B.hnnBase).toAlgHom (E.hnnBase.comp Q.hnnBase).toAlgHom
    (leftHNNFamily_base B Q D jQ haQ) (rightHNNFamily_base B Q E jB haB)
    (pairHNNExpect_fix B Q) (pairHNNExpect_left B Q)
    (positiveOfSquares D.hnnTrace D.hnnTrace_isState.2) (positiveOfSquares E.hnnTrace E.hnnTrace_isState.2)
    (reorder_base_moments B Q D E ht htD htE)
    (leftHNNFamily_free B Q D jQ hpD htD haQ hvQ)
    (rightHNNFamily_free B Q E jB hpE htE haB hvB)
    (leftHNNFamily_dense B Q D jQ hvQ) (rightHNNFamily_dense B Q E jB hvB)
    D.hnnTrace_faithful E.hnnTrace_faithful i a

theorem reorderEquiv_trace (x : D.HNNAlgebra) :
    E.hnnTrace (reorderEquiv B Q D E jQ jB ht hpD hpE htD htE haQ hvQ haB hvB x) = D.hnnTrace x :=
  jointFreeEquiv_preserves (pairHNN B Q) (leftHNNFamily B Q D jQ) (rightHNNFamily B Q E jB)
    (fun i => (pairHNNBase B Q i).toAlgHom) (pairHNNExpect B Q)
    (D.hnnBase.comp B.hnnBase).toAlgHom (E.hnnBase.comp Q.hnnBase).toAlgHom
    (leftHNNFamily_base B Q D jQ haQ) (rightHNNFamily_base B Q E jB haB)
    (pairHNNExpect_fix B Q) (pairHNNExpect_left B Q)
    (positiveOfSquares D.hnnTrace D.hnnTrace_isState.2) (positiveOfSquares E.hnnTrace E.hnnTrace_isState.2)
    (reorder_base_moments B Q D E ht htD htE)
    (leftHNNFamily_free B Q D jQ hpD htD haQ hvQ)
    (rightHNNFamily_free B Q E jB hpE htE haB hvB)
    (leftHNNFamily_dense B Q D jQ hvQ) (rightHNNFamily_dense B Q E jB hvB)
    D.hnnTrace_faithful E.hnnTrace_faithful x

end PeakingPairData

open Topology
open scoped CStarAlgebra ComplexOrder
namespace PeakingPairData

section
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (B Q : PeakingPairData A)

theorem hnn_reorder_of_peaks (D : PeakingPairData B.HNNAlgebra) (E : PeakingPairData Q.HNNAlgebra)
    (ht : ∀ a, B.trace a = Q.trace a)
    (hpD : ∀ i n, B.hnnBase (Q.peak i n) = D.peak i n)
    (hpE : ∀ i n, Q.hnnBase (B.peak i n) = E.peak i n)
    (htD : ∀ x, Q.trace (B.hnnExpectation x) = D.trace x)
    (htE : ∀ x, B.trace (Q.hnnExpectation x) = E.trace x) :
    ∃ e : D.HNNAlgebra ≃⋆ₐ[ℂ] E.HNNAlgebra,
      (∀ a, e (D.hnnBase (B.hnnBase a)) = E.hnnBase (Q.hnnBase a)) ∧
      (∀ i, e (D.hnnBase (B.hnnLetter i)) = E.hnnLetter i) ∧
      (∀ i, e (D.hnnLetter i) = E.hnnBase (Q.hnnLetter i)) ∧
      (∀ x, E.hnnTrace (e x) = D.hnnTrace x) := by
  have haD (a : A) : D.trace (B.hnnBase a) = Q.trace a := by rw [← htD,B.hnnExpectation_base]
  have haE (a : A) : E.trace (Q.hnnBase a) = B.trace a := by rw [← htE,Q.hnnExpectation_base]
  obtain ⟨jQ,_,hjQa,hjQv,_,_,_⟩ := Q.hnn_inclusion_of_peaks D B.hnnBase hpD haD
  obtain ⟨jB,_,hjBa,hjBv,_,_,_⟩ := B.hnn_inclusion_of_peaks E Q.hnnBase hpE haE
  let e := reorderEquiv B Q D E jQ jB ht hpD hpE htD htE hjQa hjQv hjBa hjBv
  have he := reorderEquiv_factor B Q D E jQ jB ht hpD hpE htD htE hjQa hjQv hjBa hjBv
  refine ⟨e,?_,?_,?_,?_⟩
  · intro a; exact (he false (B.hnnBase a)).trans (hjBa a)
  · intro i; exact (he false (B.hnnLetter i)).trans (hjBv i)
  · intro i; exact (congrArg e (hjQv i)).symm.trans (he true (Q.hnnLetter i))
  · exact reorderEquiv_trace B Q D E jQ jB ht hpD hpE htD htE hjQa hjQv hjBa hjBv

theorem hnn_reorder (hB : B.Separated) (hQ : Q.Separated) (hA : IsSimpleCStar A)
    (ht : ∀ a, B.trace a = Q.trace a) :
    let D := Q.hnnPush B hB hA ht
    let E := B.hnnPush Q hQ hA (fun a => (ht a).symm)
    ∃ e : D.HNNAlgebra ≃⋆ₐ[ℂ] E.HNNAlgebra,
      (∀ a, e (D.hnnBase (B.hnnBase a)) = E.hnnBase (Q.hnnBase a)) ∧
      (∀ i, e (D.hnnBase (B.hnnLetter i)) = E.hnnLetter i) ∧
      (∀ i, e (D.hnnLetter i) = E.hnnBase (Q.hnnLetter i)) ∧
      (∀ x, E.hnnTrace (e x) = D.hnnTrace x) := by
  apply hnn_reorder_of_peaks B Q _ _ ht (fun _ _ => rfl) (fun _ _ => rfl)
  · intro x
    change Q.trace (B.hnnExpectation x) = B.hnnTrace x
    rw [← ht]
    exact B.hnnTrace_expectation x
  · intro x
    change B.trace (Q.hnnExpectation x) = Q.hnnTrace x
    rw [ht]
    exact Q.hnnTrace_expectation x

end

section
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {C : Type*} [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  (B : PeakingPairData A)

theorem omitted_pair_classes_excluded (φ : A →⋆ₐ[ℂ] C)
    (g : A →L[ℂ] ℂ) (hg : IsPureState g)
    (F G H : C →L[ℂ] ℂ) (hF : IsPureState F) (hG : IsPureState G) (hH : IsPureState H)
    (hrF : restrictState φ F = B.state false) (hrG : restrictState φ G = g)
    (hrH : restrictState φ H = B.state true)
    (hu : StateExtensionUnique φ (B.state true))
    (hFG : PureStateEquivalent F hF G hG) (hFH : ¬ PureStateEquivalent F hF H hH) :
    (¬ PureStateEquivalent (B.state false) (B.peaks false).isPureState
      (B.state true) (B.peaks true).isPureState) ∧
    (¬ PureStateEquivalent g hg (B.state true) (B.peaks true).isPureState) := by
  constructor
  · intro h
    exact hFH (pure_lifts_equivalent φ _ _ (B.peaks false).isPureState
      (B.peaks true).isPureState h hu F H hF hH hrF hrH)
  · intro h
    exact hFH ((show UnitarilyEquivalent (pureGNS F hF) (pureGNS G hG) from hFG).trans
      (pure_lifts_equivalent φ g _ hg (B.peaks true).isPureState h hu G H hG hH hrG hrH))

theorem hnn_preserves_omitted_pair (hA : IsSimpleCStar A) (φ : A →⋆ₐ[ℂ] C)
    (g : A →L[ℂ] ℂ) (hg : IsPureState g)
    (hne : ¬ PureStateEquivalent (B.state false) (B.peaks false).isPureState g hg)
    (F G H : C →L[ℂ] ℂ) (hF : IsPureState F) (hG : IsPureState G) (hH : IsPureState H)
    (hrF : restrictState φ F = B.state false) (hrG : restrictState φ G = g)
    (hrH : restrictState φ H = B.state true)
    (hu : StateExtensionUnique φ (B.state true))
    (hFG : PureStateEquivalent F hF G hG) (hFH : ¬ PureStateEquivalent F hF H hH)
    (P Q : B.HNNAlgebra →L[ℂ] ℂ) (hP : IsPureState P) (hQ : IsPureState Q)
    (hrP : restrictState B.hnnBase P = B.state false) (hrQ : restrictState B.hnnBase Q = g) :
    ¬ PureStateEquivalent P hP Q hQ := by
  obtain ⟨h₁,h₂⟩ := B.omitted_pair_classes_excluded φ g hg F G H hF hG hH
    hrF hrG hrH hu hFG hFH
  have hs : B.Separated := by
    intro i j hij
    cases i <;> cases j
    · exact False.elim (hij rfl)
    · exact fun h => h₁ (matrix_pure_equivalence_reflects (B.state false) (B.state true)
        (B.peaks false).isPureState (B.peaks true).isPureState false true h)
    · exact fun h => h₁ (matrix_pure_equivalence_reflects (B.state false) (B.state true)
        (B.peaks false).isPureState (B.peaks true).isPureState false true h.symm)
    · exact False.elim (hij rfl)
  apply B.hnn_no_unintended_join hs hA (B.state false) g (B.peaks false).isPureState hg hne
    (fun i h => ?_) P Q hP hQ hrP hrQ
  cases i
  · exact h₂ h.2
  · exact h₁ h.1

end

end PeakingPairData

open Topology
namespace PeakingPairData
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (B Q : PeakingPairData A)

theorem separated_of_inequivalent
    (hn : ¬ PureStateEquivalent (B.state false) (B.peaks false).isPureState
      (B.state true) (B.peaks true).isPureState) : B.Separated := by
  intro i j hij h
  cases i <;> cases j
  · exact hij rfl
  · exact hn (matrix_pure_equivalence_reflects _ _ (B.peaks false).isPureState
      (B.peaks true).isPureState false true h)
  · exact hn (matrix_pure_equivalence_reflects _ _ (B.peaks false).isPureState
      (B.peaks true).isPureState false true h.symm)
  · exact hij rfl

theorem hnnPush_separated (hQ : Q.Separated) (hA : IsSimpleCStar A)
    (ht : ∀ a, Q.trace a = B.trace a)
    (hne : ¬ PureStateEquivalent (B.state false) (B.peaks false).isPureState
      (B.state true) (B.peaks true).isPureState)
    (hex : ∀ i, ¬ (PureStateEquivalent (B.state false) (B.peaks false).isPureState
        (Q.state i) (Q.peaks i).isPureState ∧
      PureStateEquivalent (B.state true) (B.peaks true).isPureState
        (Q.state (!i)) (Q.peaks (!i)).isPureState)) :
    (B.hnnPush Q hQ hA ht).Separated := by
  let E := B.hnnPush Q hQ hA ht
  apply E.separated_of_inequivalent
  apply Q.hnn_no_unintended_join hQ hA _ _ (B.peaks false).isPureState
    (B.peaks true).isPureState hne hex (E.state false) (E.state true)
    (E.peaks false).isPureState (E.peaks true).isPureState
  · exact B.pushedState_restrict Q.hnnBase Q.hnnBase_injective
      (fun i => Q.hnn_unique hQ hA _ (B.peaks i).isPureState) false
  · exact B.pushedState_restrict Q.hnnBase Q.hnnBase_injective
      (fun i => Q.hnn_unique hQ hA _ (B.peaks i).isPureState) true

theorem reordered_inclusion_pureUEP
    (D : PeakingPairData B.HNNAlgebra) (E : PeakingPairData Q.HNNAlgebra)
    (jQ : Q.HNNAlgebra →⋆ₐ[ℂ] D.HNNAlgebra)
    (jB : B.HNNAlgebra →⋆ₐ[ℂ] E.HNNAlgebra)
    (ht : ∀ a, B.trace a = Q.trace a)
    (hpD : ∀ i n, B.hnnBase (Q.peak i n) = D.peak i n)
    (hpE : ∀ i n, Q.hnnBase (B.peak i n) = E.peak i n)
    (htD : ∀ x, Q.trace (B.hnnExpectation x) = D.trace x)
    (htE : ∀ x, B.trace (Q.hnnExpectation x) = E.trace x)
    (haQ : ∀ a, jQ (Q.hnnBase a) = D.hnnBase (B.hnnBase a))
    (hvQ : ∀ i, jQ (Q.hnnLetter i) = D.hnnLetter i)
    (haB : ∀ a, jB (B.hnnBase a) = E.hnnBase (Q.hnnBase a))
    (hvB : ∀ i, jB (B.hnnLetter i) = E.hnnLetter i)
    (hQ : Q.Separated) (hE : E.Separated) (hA : IsSimpleCStar A) :
    PureUEP jQ := by
  let e := reorderEquiv B Q D E jQ jB ht hpD hpE htD htE haQ hvQ haB hvB
  have he (x : Q.HNNAlgebra) : e (jQ x) = E.hnnBase x :=
    reorderEquiv_factor B Q D E jQ jB ht hpD hpE htD htE haQ hvQ haB hvB true x
  have hh : e.symm.toStarAlgHom.comp E.hnnBase = jQ := by
    ext x
    apply e.injective
    change e (e.symm (E.hnnBase x)) = e (jQ x)
    rw [e.apply_symm_apply]
    exact (he x).symm
  rw [← hh]
  exact (show PureUEP E.hnnBase from
    fun f hf => E.hnn_unique hE (Q.hnn_simple hQ hA) f hf).postcomp_equiv e.symm

end PeakingPairData

open scoped InnerProductSpace ComplexStarModule CStarAlgebra
section
variable {A : Type*} [CStarAlgebra A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_bounded_selfAdjoint_operator_vector (d w : H)
    (hd : 1 ≤ ‖d‖) (hd' : ‖d‖ ≤ 2) (hw : (⟪d,w⟫_ℂ).im = 0) :
    ∃ T : H →L[ℂ] H, IsSelfAdjoint T ∧ T d = w ∧ ‖T‖ ≤ 12*‖w‖ := by
  let r : ℝ := ‖d‖^2
  let c : ℝ := (⟪d,w⟫_ℂ).re
  have hr : 0 < r := sq_pos_of_pos (lt_of_lt_of_le zero_lt_one hd)
  have hr1 : 1 ≤ r := by dsimp [r]; nlinarith
  have hri : 0 ≤ r⁻¹ := le_of_lt (inv_pos.mpr hr)
  have hri1 : r⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hr1
  have hc : |c| ≤ 2*‖w‖ := (Complex.abs_re_le_norm _).trans
    ((norm_inner_le_norm d w).trans (mul_le_mul_of_nonneg_right hd' (norm_nonneg _)))
  have hcr : |c/r| ≤ 2*‖w‖ := by
    rw [abs_div,abs_of_pos hr,div_eq_mul_inv]
    calc
      |c| *r⁻¹ ≤ |c| *1 := mul_le_mul_of_nonneg_left hri1 (abs_nonneg _)
      _ ≤ 2*‖w‖ := by simpa using hc
  have hdd : ⟪d,d⟫_ℂ = (r:ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; exact (Complex.ofReal_pow ‖d‖ 2).symm
  have hdw : ⟪d,w⟫_ℂ = (c:ℂ) := Complex.ext rfl hw
  have hwd : ⟪w,d⟫_ℂ = (c:ℂ) := by rw [← inner_conj_symm,hdw]; simp
  let T : H →L[ℂ] H := r⁻¹ • (InnerProductSpace.rankOne ℂ w d +
    InnerProductSpace.rankOne ℂ d w - (c/r) • InnerProductSpace.rankOne ℂ d d)
  refine ⟨T,?_,?_,?_⟩
  · change star T = T
    simp only [T,star_smul,star_trivial,star_sub,star_add,
      ContinuousLinearMap.star_eq_adjoint,InnerProductSpace.adjoint_rankOne]
    rw [add_comm]
  · simp only [T,smul_apply,sub_apply,add_apply,InnerProductSpace.rankOne_apply,
      hdd,hwd,Complex.coe_smul,smul_smul,div_mul_cancel₀ c hr.ne',
      add_sub_cancel_right,inv_mul_cancel₀ hr.ne',one_smul]
  · have hwdn : ‖w‖*‖d‖ ≤ 2*‖w‖ := by nlinarith [norm_nonneg w]
    have hdwn : ‖d‖*‖w‖ ≤ 2*‖w‖ := by nlinarith [norm_nonneg w]
    have hcdd : |c/r| *(‖d‖*‖d‖) ≤ 8*‖w‖ := by
      have hddn : ‖d‖*‖d‖ ≤ 4 := by nlinarith [norm_nonneg d]
      calc
        _ ≤ (2*‖w‖)*4 := mul_le_mul hcr hddn (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity)
        _ = _ := by ring
    calc
      ‖T‖ = r⁻¹ * ‖InnerProductSpace.rankOne ℂ w d +
        InnerProductSpace.rankOne ℂ d w - (c/r) • InnerProductSpace.rankOne ℂ d d‖ := by
          simp only [T,norm_smul,Real.norm_eq_abs,abs_of_nonneg hri]
      _ ≤ r⁻¹ * (‖InnerProductSpace.rankOne ℂ w d‖ +
        ‖InnerProductSpace.rankOne ℂ d w‖ + ‖(c/r) • InnerProductSpace.rankOne ℂ d d‖) := by
          gcongr
          exact (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
      _ ≤ r⁻¹ * (12*‖w‖) := by
          gcongr
          simp only [InnerProductSpace.norm_rankOne,norm_smul,Real.norm_eq_abs]
          linarith
      _ ≤ 12*‖w‖ := by nlinarith [norm_nonneg w]

theorem neg_saCayley_sub_one_norm (a : A) (ha : IsSelfAdjoint a) :
    ‖-saCayley a - 1‖ ≤ 2*‖a‖ := by
  have hr : ‖saResolvent a (-Complex.I)‖ ≤ 1 := by
    simpa only [Complex.neg_im,Complex.I_im,abs_neg,abs_one,inv_one] using
      saResolvent_norm_le a ha (-Complex.I) (by simp)
  have hi := (saResolvent_inverse a ha (-Complex.I) (by simp)).2
  rw [Algebra.algebraMap_eq_smul_one,neg_smul,sub_neg_eq_add] at hi
  have he : -saCayley a - 1 = -(saResolvent a (-Complex.I) * (a+a)) := by
    rw [saCayley_eq a ha]
    calc
      -(saResolvent a (-Complex.I) * (a - Complex.I • (1:A))) - 1 =
        -(saResolvent a (-Complex.I) * (a - Complex.I • (1:A))) -
          saResolvent a (-Complex.I) * (a + Complex.I • (1:A)) := by rw [hi]
      _ = _ := by noncomm_ring
  rw [he,norm_neg]
  exact (norm_mul_le _ _).trans ((mul_le_mul hr (norm_add_le a a)
    (norm_nonneg _) (by norm_num)).trans_eq (by ring))

theorem irreducible_near_unitary_vector
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (ξ η : H) (hξ : ‖ξ‖ = 1) (hη : ‖η‖ = 1) (hc : ‖ξ-η‖ ≤ 1) :
    ∃ u : unitary A, π u ξ = η ∧ ‖(u:A)-1‖ ≤ 96*‖ξ-η‖ := by
  have hd : 1 ≤ ‖ξ+η‖ := by
    have hh := norm_add_le (ξ+η) (ξ-η)
    have he : (ξ+η)+(ξ-η) = (2:ℂ) • ξ := by module
    rw [he,norm_smul,hξ,Complex.norm_ofNat,mul_one] at hh
    linarith
  have hd' : ‖ξ+η‖ ≤ 2 := (norm_add_le ξ η).trans (by rw [hξ,hη]; norm_num)
  have hi : (⟪ξ+η,Complex.I • (ξ-η)⟫_ℂ).im = 0 := by
    rw [inner_smul_right,inner_add_left,inner_sub_right,inner_sub_right]
    simp only [Complex.mul_im,Complex.I_re,Complex.I_im,zero_mul,one_mul,zero_add,
      Complex.sub_re,Complex.add_re,inner_self_eq_norm_sq_to_K]
    have hh := inner_re_symm (𝕜 := ℂ) ξ η
    change (⟪ξ,η⟫_ℂ).re = (⟪η,ξ⟫_ℂ).re at hh
    rw [hh,hξ,hη]; ring
  obtain ⟨T,hT,hTd,hTn⟩ := exists_bounded_selfAdjoint_operator_vector
    (ξ+η) (Complex.I • (ξ-η)) hd hd' hi
  obtain ⟨a,ha,han,haM⟩ := irreducible_selfAdjoint_transitivity π hπ
    (Submodule.span ℂ {ξ+η}) T hT
  have hact : π a (ξ+η) = Complex.I • (ξ-η) :=
    (haM _ (Submodule.subset_span (Set.mem_singleton _))).trans hTd
  have hre : π (a - Complex.I • (1:A)) ξ =
      π (a - (-Complex.I) • (1:A)) (-η) := by
    simp only [map_sub,map_smul,sub_apply,smul_apply,irreducible_map_one π hπ,
      one_apply_eq_self,map_neg,neg_smul,neg_apply]
    have hh : π a ξ + π a η = Complex.I • ξ - Complex.I • η := by
      simpa only [map_add,smul_sub] using hact
    rw [eq_sub_of_add_eq hh]
    abel
  let v : unitary A := ⟨saCayley a,saCayley_unitary a ha⟩
  have hv : π (v:A) ξ = -η := by
    change π (saCayley a) ξ = -η
    rw [saCayley_eq a ha,map_mul,mul_apply_eq_comp,hre,← mul_apply_eq_comp,← map_mul]
    rw [← Algebra.algebraMap_eq_smul_one,(saResolvent_inverse a ha (-Complex.I) (by simp)).2,
      irreducible_map_one π hπ,one_apply_eq_self]
  refine ⟨-v,?_,?_⟩
  · change π (-(v:A)) ξ = η
    rw [map_neg,neg_apply,hv,neg_neg]
  · change ‖-saCayley a-1‖ ≤ 96*‖ξ-η‖
    have hh := neg_saCayley_sub_one_norm a ha
    simp only [norm_smul,Complex.norm_I,one_mul] at hTn
    linarith

end

open UniformSpace
open scoped ComplexOrder
section
universe u v
variable {I : Type u} [Preorder I] [IsDirectedOrder I] [Nonempty I]
  (A : I → Type v) [∀ i, CStarAlgebra (A i)]
  (f : ∀ i j, i ≤ j → A i →⋆ₐ[ℂ] A j)
  [DirectedSystem A (f · · ·)] [IsometricStarSystem A f]
  (τ : ∀ i, A i →L[ℂ] ℂ) (hτ : ∀ i, IsState (τ i))
  (hcompat : ∀ i j h a, τ j (f i j h a) = τ i a)

local instance directLimitNormTopology : TopologicalSpace (DirectLimit A f) :=
  (inferInstance : UniformSpace (DirectLimit A f)).toTopologicalSpace

def directLimitFunctional : DirectLimit A f →L[ℂ] ℂ :=
  (DirectLimit.Module.lift ℂ I A f (fun i => (τ i).toLinearMap) hcompat).mkContinuous 1 (by
    intro a
    induction a using DirectLimit.induction f with
    | ih i a =>
      change ‖τ i a‖ ≤ 1 * ‖a‖
      simpa only [one_mul] using state_norm_apply_le (τ i) (hτ i) a)

@[simp] theorem directLimitFunctional_stage (i : I) (a : A i) :
    directLimitFunctional A f τ hτ hcompat (directLimitInclude A f i a) = τ i a := rfl

def cstarDirectLimitState : CStarDirectLimit A f →L[ℂ] ℂ :=
  (directLimitFunctional A f τ hτ hcompat).fromCompletion

@[simp] theorem cstarDirectLimitState_stage (i : I) (a : A i) :
    cstarDirectLimitState A f τ hτ hcompat (cstarDirectLimitInclude A f i a) = τ i a :=
  ContinuousLinearMap.fromCompletion_apply_coe _ _

theorem cstarDirectLimitState_isState : IsState (cstarDirectLimitState A f τ hτ hcompat) := by
  let : PartialOrder (CStarDirectLimit A f) := CStarAlgebra.spectralOrder _
  let : StarOrderedRing (CStarDirectLimit A f) := CStarAlgebra.spectralOrderedRing _
  rw [isState_iff]
  constructor
  · let i : I := Classical.choice inferInstance
    rw [← map_one (cstarDirectLimitInclude A f i),cstarDirectLimitState_stage]
    let : PartialOrder (A i) := CStarAlgebra.spectralOrder _
    let : StarOrderedRing (A i) := CStarAlgebra.spectralOrderedRing _
    exact ((isState_iff (τ i)).mp (hτ i)).1
  · intro x
    refine cstarDirectLimit_induction A f (P := fun a =>
      ((cstarDirectLimitState A f τ hτ hcompat) (star a*a)).im = 0 ∧
      0 ≤ ((cstarDirectLimitState A f τ hτ hcompat) (star a*a)).re) ?_ ?_ x
    · have hc : Continuous (fun a : CStarDirectLimit A f =>
          cstarDirectLimitState A f τ hτ hcompat (star a*a)) := by fun_prop
      exact (isClosed_eq (Complex.continuous_im.comp hc) continuous_const).inter
        (isClosed_le continuous_const (Complex.continuous_re.comp hc))
    · intro i a
      rw [← map_star,← map_mul,cstarDirectLimitState_stage]
      exact (hτ i).2 a

theorem cstarDirectLimitState_tracial (htr : ∀ i a b, τ i (a*b) = τ i (b*a))
    (x y : CStarDirectLimit A f) :
    cstarDirectLimitState A f τ hτ hcompat (x*y) =
      cstarDirectLimitState A f τ hτ hcompat (y*x) := by
  induction x, y using Completion.induction_on₂
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · rename_i x y
    rw [← Completion.coe_mul,← Completion.coe_mul]
    simp only [cstarDirectLimitState, ContinuousLinearMap.fromCompletion_apply_coe]
    induction x, y using DirectLimit.induction₂ f with
    | ih i a b =>
      rw [DirectLimit.mul_def,DirectLimit.mul_def]
      exact htr i a b

end

open scoped CStarAlgebra ComplexOrder
section
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem tracial_gns_zero_of_square_zero (τ : A →ₚ[ℂ] ℂ)
    (htr : ∀ a b, τ (a*b) = τ (b*a)) (a : A) (ha : τ (star a*a) = 0) :
    τ.gnsStarAlgHom a = 0 := by
  apply DFunLike.coe_injective
  apply (gnsVector_cyclic τ).equalizer ((τ.gnsStarAlgHom a).continuous) (by fun_prop)
  funext b
  change τ.gnsStarAlgHom a (τ.gnsStarAlgHom b (gnsVector τ)) = 0
  rw [← mul_apply_eq_comp,← map_mul]
  apply gns_vector_zero_of_square_zero
  apply norm_eq_zero.mp
  have hh := positiveTrace_sandwich τ htr (star a*a) b (star_mul_self_nonneg a)
  rw [ha,norm_zero,mul_zero] at hh
  apply le_antisymm _ (norm_nonneg _)
  simpa only [star_mul,mul_assoc] using hh

theorem tracialState_strictPos_of_simple (hA : IsSimpleCStar A)
    (τ : A →L[ℂ] ℂ) (hτ : IsState τ) (htr : ∀ a b, τ (a*b) = τ (b*a))
    (a : A) (ha : a ≠ 0) : 0 < (τ (star a*a)).re := by
  let T := positiveOfSquares τ hτ.2
  let π := T.gnsStarAlgHom
  have hn : ‖gnsVector T‖ = 1 := gnsVector_norm_eq_one T ((isState_iff τ).mp hτ).1
  have hinj : Function.Injective π := by
    apply simple_nonzeroStarHom_injective hA π.toNonUnitalStarAlgHom
    intro hz
    have hh := congrArg (fun ψ : A →⋆ₙₐ[ℂ] (T.GNS →L[ℂ] T.GNS) =>
      ψ 1 (gnsVector T)) hz
    have he : gnsVector T = 0 := by
      change π 1 (gnsVector T) = 0 at hh
      simpa only [map_one,one_apply_eq_self] using hh
    rw [he,norm_zero] at hn
    exact zero_ne_one hn
  apply lt_of_le_of_ne (hτ.2 a).2
  intro hz
  apply ha
  apply hinj
  rw [map_zero]
  apply tracial_gns_zero_of_square_zero T htr
  apply Complex.ext
  · exact hz.symm
  · exact (hτ.2 a).1

end

open Topology
section
universe u v
variable {I : Type u} [Preorder I] [IsDirectedOrder I] [Nonempty I]
  (A : I → Type v) [∀ i, CStarAlgebra (A i)]
  (f : ∀ i j, i ≤ j → A i →⋆ₐ[ℂ] A j)
  [DirectedSystem A (f · · ·)] [IsometricStarSystem A f]

theorem cstarDirectLimit_simple (hA : ∀ i, IsSimpleCStar (A i)) :
    IsSimpleCStar (CStarDirectLimit A f) := by
  let : PartialOrder (CStarDirectLimit A f) := CStarAlgebra.spectralOrder _
  let : StarOrderedRing (CStarDirectLimit A f) := CStarAlgebra.spectralOrderedRing _
  exact simple_of_dense_stage_ranges A hA (cstarDirectLimitInclude A f)
    (cstarDirectLimitInclude_isometry A f) (cstarDirectLimitInclude_dense A f)

theorem cstarDirectLimitState_strictPos (hA : ∀ i, IsSimpleCStar (A i))
    (τ : ∀ i, A i →L[ℂ] ℂ) (hτ : ∀ i, IsState (τ i))
    (hcompat : ∀ i j h a, τ j (f i j h a) = τ i a)
    (htr : ∀ i a b, τ i (a*b) = τ i (b*a))
    (a : CStarDirectLimit A f) (ha : a ≠ 0) :
    0 < (cstarDirectLimitState A f τ hτ hcompat (star a*a)).re := by
  let : PartialOrder (CStarDirectLimit A f) := CStarAlgebra.spectralOrder _
  let : StarOrderedRing (CStarDirectLimit A f) := CStarAlgebra.spectralOrderedRing _
  exact tracialState_strictPos_of_simple (cstarDirectLimit_simple A f hA)
    _ (cstarDirectLimitState_isState A f τ hτ hcompat)
    (cstarDirectLimitState_tracial A f τ hτ hcompat htr) a ha

theorem cstarDirectLimitInclude_tail_dense (i : I) :
    Dense (⋃ j : {j : I // i ≤ j}, Set.range (cstarDirectLimitInclude A f j.val)) := by
  apply (cstarDirectLimitInclude_dense A f).mono
  intro a ha
  obtain ⟨j,b,rfl⟩ := Set.mem_iUnion.mp ha
  obtain ⟨k,hik,hjk⟩ := exists_ge_ge i j
  apply Set.mem_iUnion.mpr
  exact ⟨⟨k,hik⟩,f j k hjk b,cstarDirectLimitInclude_compatible A f j k hjk b⟩

theorem cstarDirectLimit_pureUEP
    (hU : ∀ i j h, PureUEP (f i j h)) (i : I) :
    PureUEP (cstarDirectLimitInclude A f i) := by
  apply PureUEP.of_dense_cover (fun j : {j : I // i ≤ j} => A j.val)
    (cstarDirectLimitInclude A f i) (fun j => f i j.val j.property)
    (fun j => cstarDirectLimitInclude A f j.val)
  · intro j
    ext a
    exact cstarDirectLimitInclude_compatible A f i j.val j.property a
  · intro j
    exact hU i j.val j.property
  · exact cstarDirectLimitInclude_tail_dense A f i

end

open Filter Topology
open scoped CStarAlgebra ComplexOrder
namespace PeakingPairData
variable {A C : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  (D : PeakingPairData C) (φ : A →⋆ₐ[ℂ] C) (hφ : Function.Injective φ)
  (p : Bool → ℕ → A) (hp : ∀ i n, φ (p i n) = D.peak i n)

omit [PartialOrder A] [StarOrderedRing A] in
include hp in
private theorem pulled_peaks (i : Bool) : Peaks (fun n => φ (p i n)) (D.state i) := by
  simpa only [hp] using D.peaks i

def pullback : PeakingPairData A where
  trace := positivePullback D.trace φ
  tracial a b := by simp only [positivePullback_apply,map_mul]; exact D.tracial _ _
  normalized := by simpa only [positivePullback_apply,map_one] using D.normalized
  faithful a ha := by
    apply hφ
    rw [map_zero]
    apply D.faithful
    simpa only [positivePullback_apply,map_mul,map_star] using ha
  peak := p
  state i := restrictState φ (D.state i)
  peaks i := ((D.pulled_peaks φ p hp i).restrict φ hφ).1
  peak_zero i := by apply hφ; rw [hp,D.peak_zero,map_one]
  atom_positive i n := by
    change 0 < (D.trace (φ (p i n-p i (n+1)))).re
    rw [map_sub,hp,hp]
    exact D.atom_positive i n
  trace_null i := by
    simpa only [positivePullback_apply,hp] using D.trace_null i
  matched i n := by
    change D.trace (φ (p i n)) = D.trace (φ (p false n))
    rw [hp,hp,D.matched]

include hφ hp in
theorem pullback_unique (i : Bool) :
    StateExtensionUnique φ (restrictState φ (D.state i)) :=
  ((D.pulled_peaks φ p hp i).restrict φ hφ).2

theorem pullback_separated
    (hne : ¬ PureStateEquivalent (D.state false) (D.peaks false).isPureState
      (D.state true) (D.peaks true).isPureState) :
    (D.pullback φ hφ p hp).Separated := by
  let B := D.pullback φ hφ p hp
  have hn : ¬ PureStateEquivalent (B.state false) (B.peaks false).isPureState
      (B.state true) (B.peaks true).isPureState := by
    intro h
    exact hne (pure_lifts_equivalent φ _ _ (B.peaks false).isPureState
      (B.peaks true).isPureState h (D.pullback_unique φ hφ p hp true)
      (D.state false) (D.state true) (D.peaks false).isPureState (D.peaks true).isPureState rfl rfl)
  intro i j hij h
  cases i <;> cases j
  · exact hij rfl
  · exact hn (matrix_pure_equivalence_reflects _ _ (B.peaks false).isPureState
      (B.peaks true).isPureState false true h)
  · exact hn (matrix_pure_equivalence_reflects _ _ (B.peaks false).isPureState
      (B.peaks true).isPureState false true h.symm)
  · exact hij rfl

theorem pullback_hnn_inclusion :
    ∃ F : (D.pullback φ hφ p hp).HNNAlgebra →⋆ₐ[ℂ] D.HNNAlgebra,
      Function.Injective F ∧
      (∀ a, F ((D.pullback φ hφ p hp).hnnBase a) = D.hnnBase (φ a)) ∧
      (∀ i, F ((D.pullback φ hφ p hp).hnnLetter i) = D.hnnLetter i) ∧
      (∀ b, D.hnnTrace (F b) = (D.pullback φ hφ p hp).hnnTrace b) ∧
      F.range = hnnGenerated (D.hnnBase.comp φ) D.hnnLetter ∧
      (∀ b, D.hnnExpectation (F b) = φ ((D.pullback φ hφ p hp).hnnExpectation b)) :=
  (D.pullback φ hφ p hp).hnn_inclusion_of_peaks D φ hp (fun _ => rfl)

end PeakingPairData

open Topology
private noncomputable instance hnnGeneratedCStar {A C : Type*}
    [CStarAlgebra A] [CStarAlgebra C] (φ : A →⋆ₐ[ℂ] C) (w : Bool → C) :
    CStarAlgebra (hnnGenerated φ w) := by
  letI : IsClosed (hnnGenerated φ w : Set C) := hnnGenerated_isClosed φ w
  exact StarSubalgebra.cstarAlgebra (hnnGenerated φ w)

namespace PeakingPairData
attribute [local instance] hnnGenerated_isClosed
variable {A C : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  (B : PeakingPairData A) (D : PeakingPairData C)

theorem hnn_generated_step (φ : A →⋆ₐ[ℂ] C)
    (hp : ∀ i n, φ (B.peak i n) = D.peak i n)
    (ht : ∀ a, D.trace (φ a) = B.trace a)
    (hsep : B.Separated) (hA : IsSimpleCStar A) :
    ∃ e : B.HNNAlgebra ≃⋆ₐ[ℂ] hnnGenerated (D.hnnBase.comp φ) D.hnnLetter,
      (∀ a, e (B.hnnBase a) =
        hnnGeneratedBase (D.hnnBase.comp φ) D.hnnLetter a) ∧
      (∀ i, e (B.hnnLetter i) =
        hnnGeneratedLetter (D.hnnBase.comp φ) D.hnnLetter i) ∧
      (∀ x, D.hnnTrace (e x) = B.hnnTrace x) ∧
      PureUEP (hnnGeneratedBase (D.hnnBase.comp φ) D.hnnLetter) ∧
      IsSimpleCStar (hnnGenerated (D.hnnBase.comp φ) D.hnnLetter) := by
  let T := hnnGenerated (D.hnnBase.comp φ) D.hnnLetter
  obtain ⟨F,hF,hbase,hletter,htrace,hrange,_⟩ := B.hnn_inclusion_of_peaks D φ hp ht
  have hmem (x : B.HNNAlgebra) : F x ∈ T := by
    change F x ∈ hnnGenerated (D.hnnBase.comp φ) D.hnnLetter
    rw [← hrange]
    exact ⟨x,rfl⟩
  let F' : B.HNNAlgebra →⋆ₐ[ℂ] T := F.codRestrict T hmem
  have hi : Function.Injective F' := fun x y h => hF (congrArg Subtype.val h)
  have hs : Function.Surjective F' := by
    intro y
    have hy : (y : D.HNNAlgebra) ∈ F.range := by rw [hrange]; exact y.property
    obtain ⟨x,hx⟩ := hy
    exact ⟨x,Subtype.ext hx⟩
  let e : B.HNNAlgebra ≃⋆ₐ[ℂ] T := StarAlgEquiv.ofBijective F' ⟨hi,hs⟩
  have hebase (a : A) : e (B.hnnBase a) =
      hnnGeneratedBase (D.hnnBase.comp φ) D.hnnLetter a := Subtype.ext (hbase a)
  have hehom : e.toStarAlgHom.comp B.hnnBase =
      hnnGeneratedBase (D.hnnBase.comp φ) D.hnnLetter := by
    ext a
    exact congrArg Subtype.val (hebase a)
  refine ⟨e,hebase,(fun i => Subtype.ext (hletter i)),htrace,?_,?_⟩
  · rw [← hehom]
    exact (show PureUEP B.hnnBase from fun f hf => B.hnn_unique hsep hA f hf).postcomp_equiv e
  · exact (B.hnn_simple hsep hA).of_equiv e

end PeakingPairData

end NaimarkZFC

end

end OAI
