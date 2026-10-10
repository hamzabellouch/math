import OAI.NumberTheory.DirichletL.Descent.ActualChildStateSupport
import OAI.NumberTheory.DirichletL.Descent.ActualChildStateLabels

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

theorem actual_cell_triple_margins
    (hpr : ∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (hs : ActualSecondSourceConditions p source) (hk : ∀x∈source,x.second.frequency≠0)
    (d : BlockIndex) (m : O) (hm : m≠0)
    (Z r ell V M Q z c A B t j eta : ℝ) (hZ : 1<Z)
    (hparent : CanonicalMargins (r+3*ell+V) M Q z c)
    (hA : 0≤A) (ht : 0≤t) (hV : 0≤V) (hj : 0≤j) (heta : 0≤eta) (hbin : 2≤Z^eta)
    (hQ : (Ideal.absNorm (Ideal.span {m}:Ideal O).radical:ℝ)≤Z^Q)
    (h1 : ∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^(ell+eta))
    (h2 : ∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^(ell+eta))
    (hT : ∀x∈source,(Ideal.absNorm x.quotient:ℝ)≤Z^(t+eta))
    (γ : OuterTriple) (hγ : γ∈actualSecondTriples p 1 1 (cell p source d)) :
    actualSecondInheritedRadicalPuncture m γ≠0 ∧
    0≤actualSecondPunctureWidth Z m γ ∧
    ‖eisEmbedding (actualSecondInheritedRadicalPuncture m γ)‖^2=Z^(actualSecondPunctureWidth Z m γ) ∧
    CanonicalMargins (actualCellTotalExponent Z (Z^(r-A-B-t)) B j eta d)
      (childM M ell A t (secondCellExponent Z d 0) (secondCellExponent Z d 1) V j eta)
      (actualSecondPunctureWidth Z m γ) z (c-7*eta) := by
  have hn := actual_cell_triple_puncture_nonzero p hp hpr source hs d m hm γ hγ
  refine ⟨hn,?_,?_,?_⟩
  · exact Real.logb_nonneg hZ (EisensteinSchwartzPoisson.one_le_eisenstein_norm_sq _ hn)
  · exact (Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ)
      (sq_pos_of_pos (norm_pos_iff.mpr (ConcreteTraceCRT.eisEmbedding_ne_zero hn)))).symm
  · obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hγ
    have hxs := cell_subset p source d hx
    exact actual_cell_child_margins p hp hpr source hs hk d x hx 1 1 m hm
      Z r ell V M Q z c A B t j eta hZ hparent hA ht hV hj heta hbin hQ
      (h1 x hxs) (h2 x hxs) (hT x hxs)

omit hp in

theorem actual_child_enlarged_row_bounds (Z M : ℝ) (hZ : 1<Z) (k : O)
    (hk : k∈nonzeroChildFrequencyBall 1 (Z^M)) :
    k≠0 ∧ ‖eisEmbedding k‖^2≤Z^M ∧ 0≤M := by
  have hb := (mem_nonzeroChildFrequencyBall 1 one_ne_zero _ k).mp hk
  simp only [one_mul] at hb
  exact ⟨(Finset.mem_erase.mp hk).1,hb.2,actual_child_row_length_nonneg Z M hZ k hk⟩

omit hp in

theorem actual_child_size_caps (F M Q z c cap : ℝ)
    (hinv : CanonicalMargins F M Q z c) (hM : 0≤M) (hQ : 0≤Q) (hz : 0≤z)
    (hc : 0≤c) (hF : F≤cap) : M≤cap ∧ Q≤cap ∧ z≤cap := by
  obtain ⟨h1,h2⟩ := hinv
  constructor
  · linarith
  constructor <;> linarith

end SevenEighths.InverseMoment
end

end OAI
