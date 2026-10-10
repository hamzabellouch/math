import OAI.NumberTheory.DirichletL.Descent.FirstLabelCellStepChildren
import OAI.NumberTheory.DirichletL.Descent.ActualDepthBudget

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.InverseMomentFirstLabelCell
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseFirstGlobalCaps InverseSecondSourceBlocks
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι σ:Type*}[DecidableEq ι][DecidableEq σ]
variable (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]

include hp in
theorem source_total_cap (pool:Finset ι)(Q:Finset (ι→₀ℕ))(k:SourceIndex)(l j:ℕ)
    (negative:Bool)(J:Finset σ)(lists:σ→Finset ι)(Z M r ell V eta tau window b:ℝ)
    (hZ:1<Z)(heta:0≤eta)(hbin:2≤Z^eta)(hell:0≤ell)(hV:0≤V)
    (hb:1≤b)(hbt:b≤Z^(6*eta))
    (hQ:∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta)):
    let S:=source p pool Q k l j negative J lists Z M r ell V eta tau window b;
    ∀d∈keys p S,actualCellTotalExponent Z (columnScale Z r k l negative)
      (exponent Z (k 2)) (exponent Z j) eta d≤r+3*ell+V+15*eta :=by
  intro S d hd
  obtain ⟨x,hx⟩:=(mem_keys_iff p S d).mp hd
  have hn:=retained_label_numeric p hp pool Q k l j Z ell eta hZ heta hbin hQ negative J lists
    (secondCutoff p Z M r ell V eta tau window k l j negative) b (columnScale Z r k l negative)
    x (cell_subset p S d hx)
  have he:=actual_cell_child_total_upper p hp S
    (source_valid p hp pool Q k l j negative J lists Z M r ell V eta tau window b)
    (source_frequency_ne_zero p pool Q k l j negative J lists Z M r ell V eta tau window b)
    d x hx Z r ell V (columnA Z k negative) (exponent Z (k 2)) (exponent Z l) (exponent Z j) eta b hZ
    (dyadic_exponent_nonneg Z hZ _) (dyadic_exponent_nonneg Z hZ _) hell hV heta hbin hb hbt
    (source_geometry p pool Q k l j negative J lists Z M r ell V eta tau window b)
    hn.1 hn.2.1 hn.2.2.2.2.2.1
  exact he

include hp in
theorem source_state_bounds (pool:Finset ι)(Q:Finset (ι→₀ℕ))(k:SourceIndex)(l j:ℕ)
    (negative:Bool)(J:Finset σ)(lists:σ→Finset ι)(Z M r ell V eta tau window b cutoff:ℝ)
    (hZ:1<Z)(heta:0≤eta)(hbin:2≤Z^eta)(hell:0≤ell)(hV:0≤V)
    (hb:1≤b)(hbt:b≤Z^(6*eta))(hwindow:Real.exp window≤Z^(4*eta))
    (hterminal:cutoff≤ell+V)(hsmall:eta≤cutoff/16)
    (hQ:∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta)):
    let S:=source p pool Q k l j negative J lists Z M r ell V eta tau window b;
    ∀d∈keys p S,
      0≤max 0 (secondCellColumnExponent Z (columnScale Z r k l negative) d) ∧
      0≤actualCellLabelExponent Z (exponent Z (k 2)) (exponent Z j) eta d ∧
      actualCellTotalExponent Z (columnScale Z r k l negative) (exponent Z (k 2)) (exponent Z j) eta d≤r+3*ell+V+15*eta ∧
      0≤actualCellRowExponent Z M ell (columnA Z k negative) (exponent Z l) V (exponent Z j) eta d ∧
      actualCellRowExponent Z M ell (columnA Z k negative) (exponent Z l) V (exponent Z j) eta d+3*cutoff/2≤M :=by
  intro S d hd
  refine ⟨le_max_left _ _,actual_cell_label_nonneg Z _ _ eta d hZ
    (dyadic_exponent_nonneg Z hZ _) (dyadic_exponent_nonneg Z hZ _) heta,?_,?_,?_⟩
  · exact source_total_cap p hp pool Q k l j negative J lists Z M r ell V eta tau window b hZ heta hbin hell hV hb hbt hQ d hd
  · exact (source_row_gates p hp pool Q k l j negative J lists Z M r ell V eta tau window b hZ heta hbin hwindow).2 d hd
  · exact source_row_decrease p hp pool Q k l j negative J lists Z M r ell V eta tau window b cutoff hZ heta hbin hterminal hsmall hQ d hd

end SevenEighths.InverseMomentFirstLabelCell

end

end OAI
