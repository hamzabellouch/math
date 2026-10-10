import OAI.NumberTheory.DirichletL.Descent.ActualChildState
import OAI.NumberTheory.DirichletL.Descent.SecondCutoffScale
import OAI.NumberTheory.DirichletL.Descent.SecondPhysicalRows

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
open InverseSecondFibers CompletedGauss
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
include hp

theorem actual_cell_label_support {Jo Jn : ℕ}
    (source : Finset (MarkedSecondSource ι Jo Jn)) (hk : ∀x∈source,x.second.frequency≠0)
    (d : BlockIndex) (x : MarkedSecondSource ι Jo Jn) (hx : x∈cell p source d) (u v : Oˣ)
    (Z B j eta : ℝ) (hZ : 1<Z) (hbin : 2≤Z^eta)
    (hC : primeProductNorm p x.firstCommon≤Z^(B+eta))
    (hJ : ‖eisEmbedding (jLabel p x.cube.support
      (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2≤Z^(j+eta)) :
    (Ideal.absNorm (actualSecondChild p u v x).2.1:ℝ)≤Z^(actualCellLabelExponent Z B j eta d) :=
  actual_cell_child_label_power p hp source hk d x hx u v Z B j eta hZ hbin hC hJ

theorem actual_cell_correlated_row_support
    (hpr : ∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (hk : ∀x∈source,x.second.frequency≠0) (d : BlockIndex)
    (x : MarkedSecondSource ι Jo Jn) (hx : x∈cell p source d) (u v : Oˣ)
    (Z M r ell V delta A B j t eta tau L : ℝ) (hZ : 1<Z)
    (heta : 0≤eta) (hbin : 2≤Z^eta) (hL0 : 0≤L)
    (hd : ‖eisEmbedding (primeSubsetGenerator (fun i=>Ideal.span {p i}) x.firstDivisor)‖^2≤Z^(delta+eta))
    (hL : L≤Z^(r-A-B-t+4*eta))
    (hgate : x.second.frequency∈nonzeroChildFrequencyBall (actualSecondMultiplier p x)
      (correlatedSecondRadius p (primeSubsetGenerator (fun i=>Ideal.span {p i}) x.firstDivisor)
        x.second.sourceCommon x.second.divisor L
        (Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau)) (Z^tau))) :
    (actualSecondChild p u v x).2.2∈nonzeroChildFrequencyBall 1
      (Z^(childM M ell A t (secondCellExponent Z d 0) (secondCellExponent Z d 1) V j eta)) := by
  have hE := (actual_cell_norm_centers p hp source hk d x hx Z eta hZ heta hbin 1).2
  have hG := (actual_cell_norm_centers p hp source hk d x hx Z eta hZ heta hbin 0).1
  have hr := second_correlated_radius_childM p hp
    (primeSubsetGenerator (fun i=>Ideal.span {p i}) x.firstDivisor) x.second.sourceCommon x.second.divisor
    Z M r ell V delta A B j t (secondCellExponent Z d 0) (secondCellExponent Z d 1) eta tau L
    (zero_lt_one.trans hZ) hL0 hd (by simpa [outerNorms] using hE) (by simpa [outerNorms] using hG) hL
  apply (actual_second_row_ball p hp hpr x u v _).mp
  have hb := (mem_nonzeroChildFrequencyBall _ (actualSecondMultiplier_ne_zero p x) _ _).mp hgate
  exact (mem_nonzeroChildFrequencyBall _ (actualSecondMultiplier_ne_zero p x) _ _).mpr ⟨hb.1,hb.2.trans hr⟩

omit hp in

lemma actual_child_row_length_nonneg (Z M : ℝ) (hZ : 1<Z) (k : O)
    (hk : k∈nonzeroChildFrequencyBall 1 (Z^M)) : 0≤M := by
  have hb := (mem_nonzeroChildFrequencyBall 1 one_ne_zero (Z^M) k).mp hk
  simp only [one_mul] at hb
  have hk0 : k≠0 := (Finset.mem_erase.mp hk).1
  have hn := EisensteinSchwartzPoisson.one_le_eisenstein_norm_sq k hk0
  have hpow : Z^(0:ℝ)≤Z^M := by simpa only [Real.rpow_zero,one_mul] using hn.trans hb.2
  exact (Real.rpow_le_rpow_left_iff hZ).mp hpow

theorem actual_cell_row_decrease {Jo Jn : ℕ}
    (source : Finset (MarkedSecondSource ι Jo Jn)) (hs : ActualSecondSourceConditions p source)
    (hk : ∀x∈source,x.second.frequency≠0) (d : BlockIndex)
    (x : MarkedSecondSource ι Jo Jn) (hx : x∈cell p source d)
    (Z M ell A t V j eta cutoff : ℝ) (hZ : 1<Z)
    (hA : 0≤A) (ht : 0≤t) (heta : 0≤eta) (hbin : 2≤Z^eta)
    (hterminal : cutoff≤ell+V) (hsmall : eta≤cutoff/16)
    (h1 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^(ell+eta))
    (h2 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^(ell+eta))
    (hJ : Z^(j-eta)≤‖eisEmbedding (jLabel p x.cube.support
      (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) :
    childM M ell A t (secondCellExponent Z d 0) (secondCellExponent Z d 1) V j eta+3*cutoff/2≤M := by
  have hG := (actual_cell_norm_centers p hp source hk d x hx Z eta hZ heta hbin 0).2
  have hD := (actual_cell_norm_centers p hp source hk d x hx Z eta hZ heta hbin 1).1
  have hh := actual_second_row_decrease p hp x (hs.second_divisor x (cell_subset p source d hx)) Z M ell A t
    (secondCellExponent Z d 0) (secondCellExponent Z d 1) V j eta cutoff hZ hA ht hterminal hsmall
    (by simpa [outerNorms] using hG) (by simpa [outerNorms] using hD) h1 h2 hJ
  linarith

theorem actual_cell_triple_puncture_nonzero
    (hpr : ∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (hs : ActualSecondSourceConditions p source) (d : BlockIndex) (m : O) (hm : m≠0)
    (γ : OuterTriple) (hγ : γ∈actualSecondTriples p 1 1 (cell p source d)) :
    actualSecondInheritedRadicalPuncture m γ≠0 := by
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hγ
  exact radicalGenerator_ne_zero _ (actual_second_inherited_puncture_ne_zero p hp hpr x
    (hs.quotient_nonzero x (cell_subset p source d hx)) 1 1 m hm)

end SevenEighths.InverseMoment
end

end OAI
