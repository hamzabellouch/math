import OAI.Combinatorics.ContingencyTables.Machines.FiniteWordDependent

namespace OAI

/-! # Independent words for successive draws with varying widths -/

namespace ContingencyTables.FirstSuccess

open scoped BigOperators Classical
open ResidualMixture FairBits
noncomputable section

variable {X : Type*} [Fintype X] [DecidableEq X]

abbrev VaryingWords (width : ℕ → ℕ) (n : ℕ) :=
  (i : Fin n) → Fin (width i.val) → Bool

def varyingWalk (width : ℕ → ℕ)
    (step : (i : ℕ) → X → (Fin (width i) → Bool) → X) (x : X) :
    (n : ℕ) → VaryingWords width n → X
  | 0,_ => x
  | n+1,bits => step n (varyingWalk width step x n (Fin.init bits)) (bits (Fin.last n))

def varyingLaw (width : ℕ → ℕ)
    (step : (i : ℕ) → X → (Fin (width i) → Bool) → X)
    (p : RationalLaw X) : ℕ → RationalLaw X
  | 0 => p
  | n+1 => bindLaw (varyingLaw width step p n)
      (fun x => mapLaw (uniformLaw (α := Fin (width n) → Bool)) (step n x))

theorem varyingWalk_law (width : ℕ → ℕ)
    (step : (i : ℕ) → X → (Fin (width i) → Bool) → X) (x : X) (n : ℕ) :
    mapLaw (uniformLaw (α := VaryingWords width n)) (varyingWalk width step x n)=
      varyingLaw width step (pointLaw x) n := by
  induction n with
  | zero =>
    apply RationalLaw.ext
    funext y
    simp [varyingWalk,varyingLaw,pointLaw,mapLaw,uniformLaw,uniformMass,eq_comm]
  | succ n ih =>
    let E : (VaryingWords width n × (Fin (width n) → Bool)) ≃ VaryingWords width (n+1) :=
      (Equiv.prodComm _ _).trans (Fin.snocEquiv (fun i : Fin (n+1) => Fin (width i.val) → Bool))
    have hc : varyingWalk width step x (n+1) ∘ E=
        fun ab => step n (varyingWalk width step x n ab.1) ab.2 := by
      funext ab
      rcases ab with ⟨pref,last⟩
      change step n (varyingWalk width step x n (Fin.init
        (Fin.snoc (α := fun i : Fin (n+1) => Fin (width i.val) → Bool) pref last)))
        ((Fin.snoc (α := fun i : Fin (n+1) => Fin (width i.val) → Bool) pref last)
          (Fin.last n))=_
      simp only [Fin.init_snoc,Fin.snoc_last]
    apply RationalLaw.ext
    funext y
    change (mapLaw (uniformLaw (α := VaryingWords width (n+1)))
      (varyingWalk width step x (n+1))).mass y=
      (bindLaw (varyingLaw width step (pointLaw x) n)
        (fun z => mapLaw (uniformLaw (α := Fin (width n) → Bool)) (step n z))).mass y
    rw [←ih]
    simp only [bindLaw,uniform_map_mass]
    have he := uniformMapMass_equiv E (varyingWalk width step x (n+1)) y
    rw [hc] at he
    rw [←he]
    exact uniformMapMass_prod (varyingWalk width step x n) (step n) y

omit [DecidableEq X] in
private lemma bindLaw_associative (p : RationalLaw X) (q r : X → RationalLaw X) :
    bindLaw (bindLaw p q) r=bindLaw p (fun x => bindLaw (q x) r) := by
  apply RationalLaw.ext
  funext z
  simp only [bindLaw,Finset.sum_mul,Finset.mul_sum,mul_assoc]
  exact Finset.sum_comm

theorem varyingLaw_start (width : ℕ → ℕ)
    (step : (i : ℕ) → X → (Fin (width i) → Bool) → X)
    (p : RationalLaw X) (n : ℕ) :
    bindLaw p (fun x => varyingLaw width step (pointLaw x) n)=varyingLaw width step p n := by
  induction n with
  | zero =>
    apply RationalLaw.ext
    funext y
    simp [varyingLaw,bindLaw,pointLaw]
  | succ n ih =>
    change bindLaw p (fun x => bindLaw (varyingLaw width step (pointLaw x) n)
      (fun z => mapLaw (uniformLaw (α := Fin (width n) → Bool)) (step n z)))=
      bindLaw (varyingLaw width step p n)
        (fun z => mapLaw (uniformLaw (α := Fin (width n) → Bool)) (step n z))
    rw [←ih,bindLaw_associative]

def varyingWordEquiv (width : ℕ → ℕ) (n : ℕ) :
    (Fin (∑ i : Fin n,width i.val) → Bool) ≃ VaryingWords width n :=
  (Equiv.arrowCongr finSigmaFinEquiv.symm (Equiv.refl Bool)).trans
    (Equiv.piCurry (fun _ _ => Bool))

/-- The flattened word consumes exactly the sum of the successive
widths, including unused bits on any branch of the deterministic draws. -/
theorem flatVaryingWalk_law (width : ℕ → ℕ)
    (step : (i : ℕ) → X → (Fin (width i) → Bool) → X) (x : X) (n : ℕ) :
    mapLaw (uniformLaw (α := Fin (∑ i : Fin n,width i.val) → Bool))
      (fun bits => varyingWalk width step x n (varyingWordEquiv width n bits))=
      varyingLaw width step (pointLaw x) n := by
  have he := map_equiv (varyingWordEquiv width n)
    (uniformLaw (α := Fin (∑ i : Fin n,width i.val) → Bool)) (varyingWalk width step x n)
  rw [uniform_equiv] at he
  exact he.symm.trans (varyingWalk_law width step x n)

end
end ContingencyTables.FirstSuccess

end OAI
