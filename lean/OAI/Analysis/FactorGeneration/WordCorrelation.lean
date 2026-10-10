import OAI.Analysis.FactorGeneration.CoordinatePerturbation

namespace OAI

noncomputable section

namespace Generator

/-! Ordered prefix cancellation for the actual common perturbed unitary.
All identities are identities of bounded coordinate sequences. -/
section
variable {G : Type*} [Group G]

theorem prefixes_append_single (xs : List G) (x : G) :
    prefixes (xs++[x])=prefixes xs++[xs.prod*x] := by
  induction xs with
  | nil => simp [prefixes]
  | cons a xs ih => simp [prefixes,ih,List.map_append,mul_assoc]

theorem evaluated_prefixes (s : ℕ → G) (n : ℕ) :
    prefixes ((List.range n).map s)=
      (List.range n).map (fun k => FreeGroup.lift s (freePrefix (k+1))) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ,List.map_append,List.map_singleton,prefixes_append_single,ih,
      List.map_append,List.map_singleton]
    congr 2
    rw [freePrefix,map_mul,FreeGroup.lift_apply_of,freePrefix_eq_prod,map_list_prod]
    simp only [List.map_map,Function.comp_def,FreeGroup.lift_apply_of]

/-- The terminal letter is unperturbed; the same h occurs before every u. -/
theorem interleaved_terminal (t : ℕ → G) (u h : G) (n : ℕ) :
    let s : ℕ → G := fun k => if k=0 then t 0 else u*t k
    ((List.range n).map (fun k => s k*h)).prod*s n=
      t 0*((List.range n).map (fun k => h*u*t (k+1))).prod := by
  dsimp only
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.prod_range_succ,List.prod_range_succ]
    simp only [Nat.add_one_ne_zero,ite_false]
    calc
      _ = (((List.range n).map (fun k => (if k=0 then t 0 else u*t k)*h)).prod*
          (if n=0 then t 0 else u*t n))*(h*u*t (n+1)) := by simp only [mul_assoc]
      _ = _ := by rw [ih]; simp only [mul_assoc]

end
namespace Tracial

section
attribute [local instance] Classical.propDecidable Classical.decEq
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)
variable {hNM : N ≤ M} {seed : Set (Q τ ω)}

def SuccessiveCoordinateHaar.perturbedWord (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u z : unitary M.toStarSubalgebra) (ell : ℕ) (α : ℝ) : unitary (Sequences M) :=
  F.haarSequence τ ω 0*((List.range ell).map
    (fun k => F.perturbedUnitary τ ω u z ell α*F.haarSequence τ ω (k+1))).prod

theorem SuccessiveCoordinateHaar.coordinatePrefix_terminal
    (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u : unitary M.toStarSubalgebra) (ell : ℕ) :
    F.coordinatePrefix τ ω u (ell+1)=
      ((List.range ell).map (F.coordinateVariables τ ω u)).prod*
        F.coordinateVariables τ ω u ell := by
  rw [coordinatePrefix,freePrefix,(FreeGroup.lift (F.coordinateVariables τ ω u)).map_mul,
    FreeGroup.lift_apply_of,
    freePrefix_eq_prod,map_list_prod]
  simp only [List.map_map,Function.comp_def,FreeGroup.lift_apply_of]

theorem SuccessiveCoordinateHaar.perturbedWord_prefixes
    (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u z : unitary M.toStarSubalgebra) (ell : ℕ) (α : ℝ) :
    ((List.range ell).map (fun k => F.coordinatePrefix τ ω u (k+1)*
      F.perturbingUnitary τ ω u z ell α*(F.coordinatePrefix τ ω u (k+1))⁻¹)).prod*
      F.coordinatePrefix τ ω u (ell+1)=F.perturbedWord τ ω u z ell α := by
  rw [F.coordinatePrefix_terminal]
  have hp := prefix_perturbation_terminal ((List.range ell).map (F.coordinateVariables τ ω u))
    (F.perturbingUnitary τ ω u z ell α) (F.coordinateVariables τ ω u ell)
  rw [evaluated_prefixes,List.map_map] at hp
  rw [show ((List.range ell).map (fun k => F.coordinatePrefix τ ω u (k+1)*
      F.perturbingUnitary τ ω u z ell α*(F.coordinatePrefix τ ω u (k+1))⁻¹)).prod*
      (((List.range ell).map (F.coordinateVariables τ ω u)).prod*F.coordinateVariables τ ω u ell)=
      (((List.range ell).map (F.coordinateVariables τ ω u)).map
        (fun s => s*F.perturbingUnitary τ ω u z ell α)).prod*F.coordinateVariables τ ω u ell from hp]
  have hs : F.coordinateVariables τ ω u = fun k =>
      if k=0 then F.haarSequence τ ω 0 else constantSequenceUnitary u*F.haarSequence τ ω k := by
    funext k
    cases k <;> simp [coordinateVariables]
  rw [List.map_map,hs]
  exact interleaved_terminal _ _ _ ell

theorem SuccessiveCoordinateHaar.exponential_product_eq_word
    (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u z : unitary M.toStarSubalgebra) (ell : ℕ) (α : ℝ) :
    ((finitePerturbationRows ell α).map
      (fun r => NormedSpace.exp (F.perturbationMap τ ω u z ell r))).prod*
      (F.coordinatePrefix τ ω u (ell+1) : Sequences M)=
        (F.perturbedWord τ ω u z ell α : Sequences M) := by
  have hr := congrArg (fun a : unitary (Sequences M) => (a : Sequences M))
    (F.perturbedWord_prefixes τ ω u z ell α)
  rw [finitePerturbationRows,List.map_ofFn]
  simp only [Function.comp_def,F.exponential_row]
  rw [List.ofFn_eq_map]
  change ((List.finRange ell).map ((fun k : ℕ => (↑(F.coordinatePrefix τ ω u (k+1)*
    F.perturbingUnitary τ ω u z ell α*(F.coordinatePrefix τ ω u (k+1))⁻¹) : Sequences M)) ∘ Fin.val)).prod * _ = _
  rw [← List.map_map,show (List.finRange ell).map Fin.val=List.range ell from by ext i; simp]
  simpa only [Submonoid.coe_mul,Submonoid.coe_list_prod,List.map_map,Function.comp_def] using hr

end

/-! The exact first-order trace calculation for the manuscript's prefix labels. -/
section
attribute [local instance] Classical.propDecidable Classical.decEq
open UltrapowerBridge Filter
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)
variable {hNM : N ≤ M} {seed : Set (Q τ ω)}

theorem SuccessiveCoordinateHaar.label_star_trace
    (F : SuccessiveCoordinateHaar τ ω hNM seed) (u : unitary (Q τ ω))
    (hu : (u : Q τ ω) ∈ seed) (ell : ℕ) (p : PrefixLabel ell) (hp : p.val ≠ 1) :
    quotientTrace τ ω (star (F.labelUnitary τ ω u ell p : Q τ ω))=0 := by
  let f := unitaryRepresentation τ ω (prefixVariable τ ω u (fun k => (F.step k).t))
  have he : (f p.val⁻¹ : Q τ ω)=star (f p.val : Q τ ω) :=
    congrArg Subtype.val (f.map_inv p.val)
  change quotientTrace τ ω (star (f p.val : Q τ ω))=0
  rw [← he]
  exact F.freeGroup_trace τ ω u hu _ (fun h => hp (inv_eq_one.mp h))

theorem SuccessiveCoordinateHaar.conjugate_positive_correlation
    (F : SuccessiveCoordinateHaar τ ω hNM seed) (u z : unitary (Q τ ω)) (xi : Q τ ω)
    (hu : (u : Q τ ω) ∈ seed) (hz : (z : Q τ ω) ∈ seed) (hxi : xi ∈ seed)
    (ell : ℕ) (p : PrefixLabel ell) :
    quotientTrace τ ω (star xi*(F.conjugateUnitary τ ω u z ell p : Q τ ω)*
      (prefixProduct τ ω u (fun k => (F.step k).t) (ell+1) : Q τ ω))=
      if p.val=1 then quotientTrace τ ω (star xi*(z : Q τ ω)) else 0 := by
  by_cases hp : p.val=1
  · apply Eq.trans ?_ (ite_eq_left hp).symm
    have he : F.labelUnitary τ ω u ell p=1 :=
      (congrArg (unitaryRepresentation τ ω
        (prefixVariable τ ω u (fun k => (F.step k).t))) hp).trans (map_one _)
    let W := prefixProduct τ ω u (fun k => (F.step k).t) (ell+1)
    change quotientTrace τ ω (star xi*(↑(F.labelUnitary τ ω u ell p*(z*star W)*
      star (F.labelUnitary τ ω u ell p)) : Q τ ω)*(W : Q τ ω))=_
    rw [he]
    simp only [star_one,one_mul,mul_one,Submonoid.coe_mul,Unitary.coe_star,mul_assoc,
      Unitary.coe_star_mul_self]
  · apply Eq.trans ?_ (ite_eq_right hp).symm
    exact (F.prefix_endpoints τ ω u hu ell).positive_conjugate_correlation τ ω xi
      (F.seed_mem τ ω ell hxi) (F.labelUnitary τ ω u ell p) z (F.label_mem τ ω u hu ell p)
      (F.seed_mem τ ω ell hz) (F.label_star_trace τ ω u hu ell p hp)

theorem SuccessiveCoordinateHaar.conjugate_negative_correlation
    (F : SuccessiveCoordinateHaar τ ω hNM seed) (u z : unitary (Q τ ω)) (xi : Q τ ω)
    (hu : (u : Q τ ω) ∈ seed) (hz : (z : Q τ ω) ∈ seed) (hxi : xi ∈ seed)
    (ell : ℕ) (p : PrefixLabel ell) :
    quotientTrace τ ω (star xi*star (F.conjugateUnitary τ ω u z ell p : Q τ ω)*
      (prefixProduct τ ω u (fun k => (F.step k).t) (ell+1) : Q τ ω))=0 :=
  (F.prefix_endpoints τ ω u hu ell).negative_conjugate_correlation τ ω xi
    (F.seed_mem τ ω ell hxi) (F.labelUnitary τ ω u ell p) z (F.label_mem τ ω u hu ell p)
    (F.seed_mem τ ω ell hz)

def SuccessiveCoordinateHaar.firstOrderTerm
    (F : SuccessiveCoordinateHaar τ ω hNM seed) (u z : unitary (Q τ ω)) (ell : ℕ) (c : ℂ) : Q τ ω :=
  c • ∑ k : Fin ell,∑ j : Fin ell,
    ((F.conjugateUnitary τ ω u z ell (pairLabel k j) : Q τ ω)-
      star (F.conjugateUnitary τ ω u z ell (pairLabel k j) : Q τ ω))

theorem SuccessiveCoordinateHaar.firstOrder_correlation
    (F : SuccessiveCoordinateHaar τ ω hNM seed) (u z : unitary (Q τ ω)) (xi : Q τ ω)
    (hu : (u : Q τ ω) ∈ seed) (hz : (z : Q τ ω) ∈ seed) (hxi : xi ∈ seed)
    (ell : ℕ) (c : ℂ) :
    quotientTrace τ ω (star xi*F.firstOrderTerm τ ω u z ell c*
      (prefixProduct τ ω u (fun k => (F.step k).t) (ell+1) : Q τ ω))=
      c*(ell : ℂ)*quotientTrace τ ω (star xi*(z : Q τ ω)) := by
  let W := prefixProduct τ ω u (fun k => (F.step k).t) (ell+1)
  let L := (traceLinear τ ω).comp
    ((LinearMap.mulRight ℂ (W : Q τ ω)).comp (LinearMap.mulLeft ℂ (star xi)))
  have hpos (k j : Fin ell) : L (F.conjugateUnitary τ ω u z ell (pairLabel k j) : Q τ ω)=
      if k=j then quotientTrace τ ω (star xi*(z : Q τ ω)) else 0 := by
    have h := F.conjugate_positive_correlation τ ω u z xi hu hz hxi ell (pairLabel k j)
    change quotientTrace τ ω (star xi*(F.conjugateUnitary τ ω u z ell (pairLabel k j) : Q τ ω)*
      (prefixProduct τ ω u (fun k => (F.step k).t) (ell+1) : Q τ ω))=_
    simpa only [pairLabel,pairRatio_eq_one_iff] using h
  have hneg (k j : Fin ell) : L (star (F.conjugateUnitary τ ω u z ell (pairLabel k j) : Q τ ω))=0 :=
    F.conjugate_negative_correlation τ ω u z xi hu hz hxi ell (pairLabel k j)
  change L (c • ∑ k : Fin ell,∑ j : Fin ell,
    ((F.conjugateUnitary τ ω u z ell (pairLabel k j) : Q τ ω)-
      star (F.conjugateUnitary τ ω u z ell (pairLabel k j) : Q τ ω)))=_
  simp only [map_smul,map_sum,map_sub,hpos,hneg,sub_zero]
  simp [smul_eq_mul,nsmul_eq_mul,mul_assoc]

theorem SuccessiveCoordinateHaar.linearized_correlation
    (F : SuccessiveCoordinateHaar τ ω hNM seed) (u z : unitary (Q τ ω)) (xi : Q τ ω)
    (hu : (u : Q τ ω) ∈ seed) (hz : (z : Q τ ω) ∈ seed) (hxi : xi ∈ seed)
    (ell : ℕ) (c : ℂ) :
    quotientTrace τ ω (star xi*(1+F.firstOrderTerm τ ω u z ell c)*
      (prefixProduct τ ω u (fun k => (F.step k).t) (ell+1) : Q τ ω))=
      c*(ell : ℂ)*quotientTrace τ ω (star xi*(z : Q τ ω)) := by
  rw [mul_add,add_mul,trace_add,mul_one,
    (F.prefix_endpoints τ ω u hu ell).base_correlation τ ω xi (F.seed_mem τ ω ell hxi),zero_add]
  exact F.firstOrder_correlation τ ω u z xi hu hz hxi ell c

end

/-! The first-order term is exactly the sum of the mapped formal rows, and
its correlation is the manuscript's alpha/2 coefficient. -/
section
attribute [local instance] Classical.propDecidable Classical.decEq
open UltrapowerBridge Filter
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)
variable {hNM : N ≤ M} {seed : Set (Q τ ω)}

theorem SuccessiveCoordinateHaar.perturbationMap_firstOrder
    (F : SuccessiveCoordinateHaar τ ω hNM seed) (u z : unitary M.toStarSubalgebra)
    (ell : ℕ) (α : ℝ) :
    sequenceQuotient τ ω (((finitePerturbationRows ell α).map (F.perturbationMap τ ω u z ell)).sum)=
      F.firstOrderTerm τ ω (constantQuotientUnitary τ ω u) (constantQuotientUnitary τ ω z)
        ell ((α/(2*ell) : ℝ) : ℂ) := by
  let Ψ := (sequenceQuotient τ ω).toAlgHom.comp (F.perturbationMap τ ω u z ell)
  let Y := F.conjugateUnitary τ ω (constantQuotientUnitary τ ω u) (constantQuotientUnitary τ ω z) ell
  have hword (g : FreeGroup (PrefixLabel ell)) : Ψ (MonoidAlgebra.single g 1)=
      (unitaryRepresentation τ ω Y g : Q τ ω) :=
    coordinateGroupRing_quotient_single τ ω _ _ (F.coordinateConjugates_quotient τ ω u z ell) g
  have hgen (p : PrefixLabel ell) : Ψ (MonoidAlgebra.single (FreeGroup.of p) 1)=(Y p : Q τ ω) := by
    rw [hword]
    exact congrArg Subtype.val (show FreeGroup.lift Y (FreeGroup.of p)=Y p from FreeGroup.lift_apply_of)
  have hinv (p : PrefixLabel ell) : Ψ (MonoidAlgebra.single ((FreeGroup.of p)⁻¹) 1)=
      star (Y p : Q τ ω) := by
    rw [hword,(unitaryRepresentation τ ω Y).map_inv]
    change star (FreeGroup.lift Y (FreeGroup.of p) : Q τ ω)=_
    rw [FreeGroup.lift_apply_of]
  have hs (r : ℝ) (a : MonoidAlgebra ℂ (FreeGroup (PrefixLabel ell))) : Ψ (r • a)=r • Ψ a :=
    map_smul (Ψ.restrictScalars ℝ).toLinearMap r a
  have hrow (k : Fin ell) : Ψ (finitePerturbationRow α k)=
      (α/(2*ell) : ℝ) • ∑ j : Fin ell,((Y (pairLabel k j) : Q τ ω)-star (Y (pairLabel k j) : Q τ ω)) := by
    rw [finitePerturbationRow,hs]
    congr 1
    simp only [map_sum,map_sub,hgen,hinv]
  change (sequenceQuotient τ ω) (((List.ofFn (finitePerturbationRow (n := ell) α)).map
    (F.perturbationMap τ ω u z ell)).sum)=_
  rw [List.map_ofFn,List.sum_ofFn,map_sum]
  change (∑ k : Fin ell,Ψ (finitePerturbationRow α k))=_
  simp only [hrow,← Finset.smul_sum]
  exact (IsScalarTower.algebraMap_smul ℂ (α/(2*ell) : ℝ) _).symm

theorem SuccessiveCoordinateHaar.coordinate_linearized_correlation
    (F : SuccessiveCoordinateHaar τ ω hNM seed) (u z : unitary M.toStarSubalgebra)
    (xi : Q τ ω)
    (hu : (constantQuotientUnitary τ ω u : Q τ ω) ∈ seed)
    (hz : (constantQuotientUnitary τ ω z : Q τ ω) ∈ seed) (hxi : xi ∈ seed)
    (ell : ℕ) (hell : 0 < ell) (α : ℝ) :
    quotientTrace τ ω (star xi*(1+sequenceQuotient τ ω
      (((finitePerturbationRows ell α).map (F.perturbationMap τ ω u z ell)).sum))*
      (prefixProduct τ ω (constantQuotientUnitary τ ω u) (fun k => (F.step k).t) (ell+1) : Q τ ω))=
      (α : ℂ)/2*quotientTrace τ ω (star xi*(constantQuotientUnitary τ ω z : Q τ ω)) := by
  rw [F.perturbationMap_firstOrder,F.linearized_correlation τ ω _ _ xi hu hz hxi]
  have hn : (ell : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hell)
  push_cast
  field_simp [hn]

end

/-! The uniform trace correlation for the actual product of coordinate
exponentials. Identifying that product with a single-unitary perturbation word
is a separate remaining step. -/
section
attribute [local instance] Classical.propDecidable Classical.decEq
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)
variable {hNM : N ≤ M} {seed : Set (Q τ ω)}

theorem SuccessiveCoordinateHaar.exponential_product_correlation
    (F : SuccessiveCoordinateHaar τ ω hNM seed) (u z : unitary M.toStarSubalgebra)
    (xi : Q τ ω)
    (hu : (constantQuotientUnitary τ ω u : Q τ ω) ∈ seed)
    (hz : (constantQuotientUnitary τ ω z : Q τ ω) ∈ seed) (hxi : xi ∈ seed)
    (ell : ℕ) (hell : 0 < ell) (α : ℝ) (hα : 0 < α) (hhalf : α < 1/2) :
    ‖quotientTrace τ ω (star xi*(sequenceQuotient τ ω
      (((finitePerturbationRows ell α).map (fun r => NormedSpace.exp (F.perturbationMap τ ω u z ell r))).prod)*
      (prefixProduct τ ω (constantQuotientUnitary τ ω u) (fun k => (F.step k).t) (ell+1) : Q τ ω)))-
      (α : ℂ)/2*quotientTrace τ ω (star xi*(constantQuotientUnitary τ ω z : Q τ ω))‖ ≤
        ‖xi‖*(4*α^2/(1-2*α)) := by
  let W := prefixProduct τ ω (constantQuotientUnitary τ ω u) (fun k => (F.step k).t) (ell+1)
  apply quotient_correlation_remainder τ ω xi _ _ (W : Q τ ω) _ _
    (Unitary.coe_mul_star_self W)
  · simpa only [mul_assoc] using F.coordinate_linearized_correlation τ ω u z xi hu hz hxi ell hell α
  · have h := F.perturbation_remainder τ ω u z hu hz ell hell α hα hhalf
    simpa only [remainderSequence,map_sub,map_one,sub_add_eq_sub_sub] using h

end

/-! The uniform correlation now belongs to the literal word in one common
perturbed unitary, as required by eq:perturbation-prefix. -/
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)
variable {hNM : N ≤ M} {seed : Set (Q τ ω)}

theorem SuccessiveCoordinateHaar.coordinatePrefix_quotient
    (F : SuccessiveCoordinateHaar τ ω hNM seed) (u : unitary M.toStarSubalgebra) (k : ℕ) :
    sequenceUnitaryQuotient τ ω (F.coordinatePrefix τ ω u k)=
      prefixProduct τ ω (constantQuotientUnitary τ ω u) (fun j => (F.step j).t) k := by
  rw [coordinatePrefix,freeGroup_quotient τ ω _ _ (F.coordinateVariables_quotient τ ω u),
    unitaryRepresentation_prefix]

theorem SuccessiveCoordinateHaar.perturbedWord_correlation
    (F : SuccessiveCoordinateHaar τ ω hNM seed) (u z : unitary M.toStarSubalgebra)
    (xi : Q τ ω)
    (hu : (constantQuotientUnitary τ ω u : Q τ ω) ∈ seed)
    (hz : (constantQuotientUnitary τ ω z : Q τ ω) ∈ seed) (hxi : xi ∈ seed)
    (ell : ℕ) (hell : 0 < ell) (α : ℝ) (hα : 0 < α) (hhalf : α < 1/2) :
    ‖quotientTrace τ ω (star xi*sequenceQuotient τ ω
        (F.perturbedWord τ ω u z ell α : Sequences M))-
      (α : ℂ)/2*quotientTrace τ ω (star xi*(constantQuotientUnitary τ ω z : Q τ ω))‖ ≤
        ‖xi‖*(4*α^2/(1-2*α)) := by
  rw [← F.exponential_product_eq_word,map_mul]
  have hp := congrArg Subtype.val (F.coordinatePrefix_quotient τ ω u (ell+1))
  change sequenceQuotient τ ω (F.coordinatePrefix τ ω u (ell+1) : Sequences M)=_ at hp
  rw [hp]
  exact F.exponential_product_correlation τ ω u z xi hu hz hxi ell hell α hα hhalf

end Tracial

end Generator

end

end OAI
