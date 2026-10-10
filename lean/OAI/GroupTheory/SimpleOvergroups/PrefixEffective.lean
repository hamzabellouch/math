import Mathlib
import OAI.GroupTheory.SimpleOvergroups.PrefixLists

namespace OAI


namespace BinaryPrefixOperators.Arithmetic.Lists
variable {K : Type*} [CommRing K] [Primcodable K] [Finite K] [DecidableEq K]

private theorem prim_add {K : Type*} [CommRing K] [Primcodable K] [Finite K]
    [DecidableEq K] : Primrec₂ ((· + ·) : K → K → K) :=
  (Primrec.dom_finite (fun p : K × K => p.1+p.2)).to₂

 theorem primrec_coefficient : Primrec₂ (coefficient (K:=K)) := by
  change Primrec (fun p : Poly K × Pair =>
    p.1.foldr (fun x a => (if x.2 = p.2 then x.1 else 0) + a) 0)
  apply Primrec.list_foldr (h := fun (p : Poly K × Pair) (a : (K × Pair) × K) =>
    (if a.1.2 = p.2 then a.1.1 else 0) + a.2) Primrec.fst (Primrec.const 0)
  exact (prim_add.comp
    (Primrec.ite (Primrec.eq.comp
      (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.fst))
      (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)) (Primrec.const 0))
    (Primrec.snd.comp Primrec.snd)).to₂

 theorem primrec_isZero : Primrec (isZero (K:=K)) := by
  have hr : PrimrecRel (fun (a : K × Pair) (p : Poly K) => coefficient p a.2 = 0) :=
    Primrec.eq.comp (primrec_coefficient.comp Primrec.snd (Primrec.snd.comp Primrec.fst))
      (Primrec.const 0)
  have hp : PrimrecPred (fun p : Poly K => ∀ a ∈ p, coefficient p a.2 = 0) :=
    hr.forall_mem_list.comp Primrec.id Primrec.id
  exact hp.decide.of_eq fun p => by
    apply Bool.eq_iff_iff.mpr
    simp [isZero]

 theorem primrec_suffixes : Primrec suffixes := by
  have h0 : Primrec (fun _ : Unit => ([[]] : List Word)) := Primrec.const _
  have hs : Primrec₂ (fun (_ : Unit) (p : ℕ × List Word) =>
      p.2.map (0::·) ++ p.2.map (1::·)) := by
    exact (Primrec.list_append.comp
      (Primrec.list_map (Primrec.snd.comp Primrec.snd)
        (Primrec.list_cons.comp (Primrec.const 0) Primrec.snd).to₂)
      (Primrec.list_map (Primrec.snd.comp Primrec.snd)
        (Primrec.list_cons.comp (Primrec.const 1) Primrec.snd).to₂)).to₂
  refine ((Primrec.nat_rec h0 hs).comp (Primrec.const ()) Primrec.id).of_eq ?_
  intro n
  dsimp only [id, Prod.snd]
  induction n with
  | zero => rfl
  | succ n ih => simp [suffixes, ih]

 theorem primrec_expandTerm {K : Type*} [CommRing K] [Primcodable K] [Finite K]
    [DecidableEq K] : Primrec₂ (expandTerm (K:=K)) := by
  unfold expandTerm
  apply Primrec.list_map (primrec_suffixes.comp Primrec.fst)
  exact ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair
    ((Primrec.list_append.comp
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))) Primrec.snd).pair
    (Primrec.list_append.comp
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))) Primrec.snd))).to₂

 theorem primrec_depth {K : Type*} [CommRing K] [Primcodable K] [Finite K]
    [DecidableEq K] : Primrec (depth (K:=K)) := by
  have h : Primrec (fun p : Poly K =>
      p.foldr (fun a b => max a.2.2.length b) 0) :=
    Primrec.list_foldr Primrec.id (Primrec.const 0)
      (Primrec.nat_max.comp
        (Primrec.list_length.comp (Primrec.snd.comp (Primrec.snd.comp
          (Primrec.fst.comp Primrec.snd)))) (Primrec.snd.comp Primrec.snd)).to₂
  refine h.of_eq ?_
  intro p
  induction p with
  | nil => rfl
  | cons a p ih => simp [depth, ih]

 theorem primrec_spread : Primrec₂ (spread (K:=K)) := by
  unfold spread
  apply Primrec.list_flatMap Primrec.snd
  exact (primrec_expandTerm.comp
    (Primrec.nat_sub.comp (Primrec.fst.comp Primrec.fst)
      (Primrec.list_length.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
    Primrec.snd).to₂

 theorem primrec_zeroTest : Primrec (zeroTest (K:=K)) :=
  primrec_isZero.comp (primrec_spread.comp primrec_depth Primrec.id)

theorem computable_zero : ComputablePred
    (fun p : Poly K => evaluate K (toArray p) = 0) :=
  (show ComputablePred (fun p : Poly K => zeroTest p = true) from
    ⟨inferInstance, (Primrec.eq.comp primrec_zeroTest (Primrec.const true)).decide.to_comp⟩).of_eq
    (fun p => zeroTest_iff p)

end BinaryPrefixOperators.Arithmetic.Lists

end OAI
