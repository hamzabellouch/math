import Mathlib
import OAI.Combinatorics.KMedianRecovery.Encoding.LabelSize
import OAI.Combinatorics.KMedianRecovery.Recovery.PolynomialProduct
import OAI.Combinatorics.KMedianRecovery.Sampling.SamplerContext
import OAI.Combinatorics.KMedianRecovery.Encoding.BoundedNatWord

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySampler.Parameters
open WordOperations WordList BinaryArithmetic Polynomial RadiusMenus Sampling Sampling.Comparison
open BinaryOpeningPayment (field field_computes field_encode)
noncomputable def M : ℕ := firstSize mainKappa
noncomputable def E : ℕ := geometricCap mainKappa mainKappa_pos
lemma thirdSize_eq (m : ℕ) : thirdSize mainKappa m=1+2000000*m := by
  unfold thirdSize mainKappa
  have he : 2*(m:ℝ)/(1/1000000)=(2000000*m:ℕ) := by push_cast; ring
  rw [he, Nat.ceil_natCast]
def pack {n : ℕ} (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℕ) (P : ℚ) (m : ℕ) : List Bool :=
  encode [RationalMatrix.encode δ,List.replicate n true,BinaryFinSet.encode D,BinaryFinSet.encode F,
    BinaryFinSet.encode S,Δ.bits,BinaryRational.encode P,m.bits]
noncomputable def bound : Polynomial ℕ := X+C (⌈20/(IntegralAssembly.gamma/16)⌉₊+2)*(X+2)^2
noncomputable def unary (j : ℕ) (x : List Bool) : List Bool := BoundedNatWord.run bound (pairBits (field j x,x))
attribute [local irreducible] BoundedNatWord.run bound
noncomputable def unary_computes (j : ℕ) : PolyComputes (unary j) :=
  ((field_computes j).pair id_computes).comp (BoundedNatWord.run_computes bound)
noncomputable def Jword (x : List Bool) : List Bool := [true]++RepeatedAppend.copies (unary 7 x).length (List.replicate 2000000 true)
noncomputable def Jword_computes : PolyComputes Jword :=
  (const_computes [true]).append (UnaryResources.copy_computes (unary_computes 7) (const_computes (List.replicate 2000000 true)))
noncomputable def nword (x : List Bool) : List Bool := Count.run (field 2 x)
noncomputable def nword_computes : PolyComputes nword := (field_computes 2).comp Count.run_computes
noncomputable def precision (x : List Bool) : List Bool :=
  nword x++unary 5 x++List.replicate M true++List.replicate E true++Jword x++List.replicate 5 true
noncomputable def precision_computes : PolyComputes precision :=
  (((nword_computes.append (unary_computes 5)).append (const_computes (List.replicate M true))).append
    (const_computes (List.replicate E true))).append Jword_computes |>.append (const_computes (List.replicate 5 true))
noncomputable def menus (x : List Bool) : List Bool := encode [List.replicate M true,List.replicate E true,Jword x]
noncomputable def menus_computes : PolyComputes menus := cons_computes (const_computes (List.replicate M true))
  (cons_computes (const_computes (List.replicate E true)) (cons_computes Jword_computes (const_computes [])))
noncomputable def dimension (x : List Bool) : List Bool := UnaryResources.lengthBits (field 1 x)
noncomputable def dimension_computes : PolyComputes dimension := (field_computes 1).comp UnaryResources.lengthBits_computes
noncomputable def diameter (x : List Bool) : List Bool := BinaryRational.natWords (field 5 x)
noncomputable def diameter_computes : PolyComputes diameter := (field_computes 5).comp BinaryRational.natWords_computes
noncomputable def run (x : List Bool) : List Bool := encode [dimension x,field 0 x,field 2 x,field 3 x,field 4 x,
  diameter x,field 6 x,BinaryRational.encode (1/1000000),field 7 x,menus x]
noncomputable def run_computes : PolyComputes run := list_computes
  [dimension,field 0,field 2,field 3,field 4,diameter,field 6,fun _=>BinaryRational.encode (1/1000000),field 7,menus] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact ⟨dimension_computes⟩
    · exact ⟨field_computes 0⟩
    · exact ⟨field_computes 2⟩
    · exact ⟨field_computes 3⟩
    · exact ⟨field_computes 4⟩
    · exact ⟨diameter_computes⟩
    · exact ⟨field_computes 6⟩
    · exact ⟨const_computes _⟩
    · exact ⟨field_computes 7⟩
    · exact ⟨menus_computes⟩)
variable {n : ℕ}
lemma pack_resources (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℕ) (P : ℚ) (m : ℕ)
    (hm : m≤n) (hΔ : Δ≤Rounding.cap D.card (IntegralAssembly.gamma/16)) :
    m≤bound.eval (pack δ D F S Δ P m).length ∧ Δ≤bound.eval (pack δ D F S Δ P m).length := by
  let L := (pack δ D F S Δ P m).length
  have hn : n≤L := by
    have hh:=member_length (show List.replicate n true∈[RationalMatrix.encode δ,List.replicate n true,
      BinaryFinSet.encode D,BinaryFinSet.encode F,BinaryFinSet.encode S,Δ.bits,BinaryRational.encode P,m.bits] by simp)
    simpa only [L,pack,List.length_replicate] using hh
  have hd : D.card≤L := (Finset.card_le_univ D).trans (by simpa only [Finset.card_univ,Fintype.card_fin] using hn)
  have hc:=GlobalAssembly.cap_polynomial D.card L hd
  simp only [bound,eval_add,eval_X,eval_mul,eval_C,eval_pow,eval_ofNat]
  exact ⟨(hm.trans hn).trans (Nat.le_add_right _ _),(hΔ.trans hc).trans (Nat.le_add_left _ _)⟩
lemma unary_pack (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℕ) (P : ℚ) (m : ℕ)
    (hm : m≤n) (hΔ : Δ≤Rounding.cap D.card (IntegralAssembly.gamma/16)) :
    unary 7 (pack δ D F S Δ P m)=List.replicate m true ∧
    unary 5 (pack δ D F S Δ P m)=List.replicate Δ true := by
  obtain ⟨hm',hd'⟩:=pack_resources δ D F S Δ P m hm hΔ
  constructor
  · simpa only [unary,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
      using BoundedNatWord.run_exact bound m (pack δ D F S Δ P m) hm'
  · simpa only [unary,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
      using BoundedNatWord.run_exact bound Δ (pack δ D F S Δ P m) hd'
lemma Jword_pack (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℕ) (P : ℚ) (m : ℕ)
    (hm : m≤n) (hΔ : Δ≤Rounding.cap D.card (IntegralAssembly.gamma/16)) :
    Jword (pack δ D F S Δ P m)=List.replicate (thirdSize mainKappa m) true := by
  rw [Jword,(unary_pack δ D F S Δ P m hm hΔ).1,List.length_replicate,thirdSize_eq]
  have he (k : ℕ) : RepeatedAppend.copies k (List.replicate 2000000 true)=List.replicate (2000000*k) true := by
    induction k with
    | zero=>rfl
    | succ k ih=>simp only [RepeatedAppend.copies,ih,←List.replicate_add]; congr 1
  rw [he]
  exact (List.replicate_add 1 _ true).symm
lemma precision_pack (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℕ) (P : ℚ) (m : ℕ)
    (hm : m≤n) (hΔ : Δ≤Rounding.cap D.card (IntegralAssembly.gamma/16)) :
    precision (pack δ D F S Δ P m)=List.replicate (integralPrecision D (Δ:ℝ) m) true := by
  rw [precision,(unary_pack δ D F S Δ P m hm hΔ).2,Jword_pack δ D F S Δ P m hm hΔ]
  simp only [nword,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    BinaryFinSet.encode_eq,Count.run_encode,List.length_map,Finset.length_sort,integralPrecision,
    Nat.ceil_natCast,precisionBits,M,E,←List.replicate_add]
lemma run_pack (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℕ) (P : ℚ) (m : ℕ)
    (hm : m≤n) (hΔ : Δ≤Rounding.cap D.card (IntegralAssembly.gamma/16)) :
    run (pack δ D F S Δ P m)=config δ D F S Δ P (1/1000000) m M E (thirdSize mainKappa m) := by
  rw [run,menus,Jword_pack δ D F S Δ P m hm hΔ]
  simp only [dimension,diameter,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    UnaryResources.lengthBits_eq,List.length_replicate,BinaryRational.natWords_bits,config,BinaryMenu.weights]
end MetricKMedianRecovery.BitMachine.BinarySampler.Parameters

end OAI
