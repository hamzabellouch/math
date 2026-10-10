import OAI.Combinatorics.ContingencyTables.Machines.FixedCardinalityLaw
import OAI.Combinatorics.ContingencyTables.Transport.FiniteRationalThreshold
import OAI.Combinatorics.ContingencyTables.Transport.FiniteLawMoments
import OAI.Combinatorics.ContingencyTables.Machines.FiniteWordDependent
import OAI.Combinatorics.ContingencyTables.Transport.RationalMapProducts

namespace OAI

/-! # Bounded Boolean implementation of fixed-cardinality subset draws -/

namespace ContingencyTables.FixedCardinalityBits

open CommonBasesFPRAS ResidualMixture FirstSuccess FairBits FixedCardinalityLaw
open scoped BigOperators Classical
noncomputable section

def headDraw (B n k : ℕ) (bits : Fin B → Bool) : Bool :=
  decide (rationalThresholdAccept B (headProbability n k) bits)

def roundedHeadLaw (B n k : ℕ) : RationalLaw Bool :=
  mapLaw (uniformLaw (α := Fin B → Bool)) (headDraw B n k)

lemma roundedHead_true (B n k : ℕ) :
    (roundedHeadLaw B n k).mass true=rationalThresholdMass B (headProbability n k) := by
  have hword := FiniteLawMoments.word_expectation (headDraw B n k)
    (fun b => if b then (1:ℝ) else 0)
  have hfun : (fun bits : Fin B → Bool => if headDraw B n k bits then (1:ℝ) else 0)=
      (fun bits => if rationalThresholdAccept B (headProbability n k) bits then (1:ℝ) else 0) := by
    funext bits
    simp [headDraw]
  rw [hfun] at hword
  have ht := rationalThreshold_expectation B (headProbability n k)
    (headProbability_bounds n k).1 (headProbability_bounds n k).2
  have he := hword.symm.trans ht
  have hc : ((roundedHeadLaw B n k).mass true:ℝ)=
      (rationalThresholdMass B (headProbability n k):ℝ) := by
    simpa [FiniteLawMoments.expectation,Fintype.sum_bool,roundedHeadLaw] using he
  exact_mod_cast hc

private lemma bool_variation (p q : RationalLaw Bool) :
    variation p q=|p.mass true-q.mass true| := by
  have hp := p.total
  have hq := q.total
  rw [Fintype.sum_bool] at hp hq
  have hf : p.mass false-q.mass false= -(p.mass true-q.mass true) := by linarith
  unfold variation
  rw [Fintype.sum_bool,hf,abs_neg]
  ring

theorem roundedHead_error (B n k : ℕ) :
    variation (roundedHeadLaw B n k) (headLaw n k)≤1/(2:ℚ)^B := by
  rw [bool_variation,roundedHead_true]
  change |rationalThresholdMass B (headProbability n k)-headProbability n k|≤_
  have he := rationalThreshold_error B (headProbability n k) (headProbability_bounds n k).1
  rw [abs_of_nonpos (sub_nonpos.mpr he.2.1)]
  linarith [he.2.2]

def roundedFixedLaw (B : ℕ) : (n k : ℕ) → RationalLaw (Fin n → Bool)
  | 0, _ => pointLaw (fun i => Fin.elim0 i)
  | n+1, k => consLaw (roundedHeadLaw B n k)
      (fun b => roundedFixedLaw B n (remaining n k b))

theorem roundedFixed_error (B n k : ℕ) :
    variation (roundedFixedLaw B n k) (fixedLaw n k)≤(n:ℚ)/(2:ℚ)^B := by
  induction n generalizing k with
  | zero => simp [roundedFixedLaw,fixedLaw,variation]
  | succ n ih =>
    change variation (consLaw (roundedHeadLaw B n k) _)
      (consLaw (headLaw n k) _)≤_
    have hh := consLaw_variation (roundedHeadLaw B n k) (headLaw n k)
      (fun b => roundedFixedLaw B n (remaining n k b))
      (fun b => fixedLaw n (remaining n k b)) ((n:ℚ)/(2:ℚ)^B)
      (fun b => ih (remaining n k b))
    calc
      _ ≤ variation (roundedHeadLaw B n k) (headLaw n k)+(n:ℚ)/(2:ℚ)^B := hh
      _ ≤ 1/(2:ℚ)^B+(n:ℚ)/(2:ℚ)^B :=
        _root_.add_le_add (roundedHead_error B n k) le_rfl
      _ = _ := by push_cast; ring

def draw (B : ℕ) : (n k : ℕ) → (Fin n → Fin B → Bool) → (Fin n → Bool)
  | 0, _, _ => fun i => Fin.elim0 i
  | n+1, k, words =>
      let b := headDraw B n k (words 0)
      Fin.cons b (draw B n (remaining n k b) (Fin.tail words))

private theorem consWordLaw {W V : Type*} [Fintype W] [Fintype V]
    [Nonempty W] [Nonempty V] {n : ℕ} (f : W → Bool)
    (g : Bool → V → (Fin n → Bool)) :
    mapLaw (productLaw (uniformLaw (α := W)) (uniformLaw (α := V)))
      (fun ab => Fin.cons (f ab.1) (g (f ab.1) ab.2))=
    consLaw (mapLaw (uniformLaw (α := W)) f)
      (fun b => mapLaw (uniformLaw (α := V)) (g b)) := by
  change mapLaw _ (fun ab : W×V => consEquiv n (⟨f ab.1,g (f ab.1) ab.2⟩ :
    (_b : Bool) × (Fin n → Bool)))=_
  rw [mapLaw_equiv_output,mapLaw_dependent_product]
  rfl

theorem draw_law (B n k : ℕ) :
    mapLaw (uniformLaw (α := Fin n → Fin B → Bool)) (draw B n k)=
      roundedFixedLaw B n k := by
  induction n generalizing k with
  | zero =>
    apply RationalLaw.ext
    funext v
    simp [draw,roundedFixedLaw,mapLaw,uniformLaw,uniformMass,pointLaw,eq_comm]
  | succ n ih =>
    let E := Fin.consEquiv (fun _ : Fin (n+1) => Fin B → Bool)
    have he := map_equiv E
      (uniformLaw (α := (Fin B → Bool)×(Fin n → Fin B → Bool))) (draw B (n+1) k)
    rw [uniform_equiv,←uniform_product] at he
    have hf : (fun ab => draw B (n+1) k (E ab))=
        (fun ab => Fin.cons (headDraw B n k ab.1)
          (draw B n (remaining n k (headDraw B n k ab.1)) ab.2)) := by
      funext ab
      simp only [draw,E,Fin.consEquiv,Equiv.coe_fn_mk,Fin.cons_zero,Fin.tail_cons]
    rw [hf] at he
    have hc := consWordLaw (headDraw B n k)
      (fun b => draw B n (remaining n k b))
    have htail :
        (fun b => mapLaw (uniformLaw (α := Fin n → Fin B → Bool))
          (draw B n (remaining n k b)))=
        (fun b => roundedFixedLaw B n (remaining n k b)) := by
      funext b
      exact ih (remaining n k b)
    rw [htail] at hc
    exact he.trans hc

def blockWords (n B : ℕ) : (Fin (n*B) → Bool) ≃ (Fin n → Fin B → Bool) :=
  (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bool)).trans (Equiv.curry _ _ _)

def bitDraw (B n k : ℕ) (bits : Fin (n*B) → Bool) : Fin n → Bool :=
  draw B n k (blockWords n B bits)

theorem bitDraw_law (B n k : ℕ) :
    mapLaw (uniformLaw (α := Fin (n*B) → Bool)) (bitDraw B n k)=
      roundedFixedLaw B n k := by
  have he := map_equiv (blockWords n B)
    (uniformLaw (α := Fin (n*B) → Bool)) (draw B n k)
  rw [uniform_equiv] at he
  exact he.symm.trans (draw_law B n k)

/-- Exactly nB fair bits implement the sequential subset draw with
total variation error at most n/2^B, uniformly in the requested size. -/
theorem bitDraw_error (B n k : ℕ) :
    variation (mapLaw (uniformLaw (α := Fin (n*B) → Bool)) (bitDraw B n k))
      (fixedLaw n k)≤(n:ℚ)/(2:ℚ)^B := by
  rw [bitDraw_law]
  exact roundedFixed_error B n k

end
end ContingencyTables.FixedCardinalityBits

end OAI
