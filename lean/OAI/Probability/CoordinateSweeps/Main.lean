import Mathlib
import OAI.Probability.CoordinateSweeps.Perturbation

namespace OAI

open scoped Matrix.Norms.L2Operator
namespace CoordinateSweeps
lemma moment_le_exp_of_logMoment_le {t B : ℝ} (ht : 0≤t)
    (h : logMoment t ≤ (B:EReal)) : t ≤ Real.exp B := by
  by_cases hz : t=0
  · rw [hz]; exact (Real.exp_pos _).le
  · rw [logMoment,ite_eq_right hz] at h
    have hh : Real.log t ≤ B := by exact_mod_cast h
    simpa only [Real.exp_log (lt_of_le_of_ne ht (Ne.symm hz))] using Real.exp_le_exp.mpr hh
lemma logMoment_le_of_moment_le_exp {t B : ℝ} (ht : 0≤t) (h : t≤Real.exp B) :
    logMoment t ≤ (B:EReal) := by
  simpa only [Real.log_exp] using logMoment_le_of_le ht (Real.exp_pos B) h
end CoordinateSweeps
namespace CoordinateSweeps.Grid.Holes
open SparseScalar SparseDimension ScalarInduction
variable {G : Grid} {h r : ℕ} (H : G.Holes h)
lemma conditionalAverage_free_cancel (hf : H.Feasible) (z : ℝ) (σ : UnitaryIrrep H.stabilizer) :
    H.conditionalAverage hf z ((σ.pullback H.stabilizerFreeEquiv.symm).pullback H.stabilizerFreeEquiv)=
      H.conditionalAverage hf z σ := by
  rw [H.conditionalAverage_eq_sum,H.conditionalAverage_eq_sum]
  apply Finset.sum_congr rfl
  intro ω hω
  change (_:ℂ) • σ.matrix (H.stabilizerFreeEquiv.symm (H.stabilizerFreeEquiv (H.residual hf ω)))=_
  rw [MulEquiv.symm_apply_apply]
/-- Entire nonautomatic sparse-dimension branch of the conditional main,
with the actual stabilizer irrep, actual feasible paths and a common real z interval. -/
theorem conditional_sparse_main (hr : ScaleLarge r) (hrS : ScaleReady r)
    (hG : G.Allowed r) (hS : MainSizeReady SparseScalar.q G.size)
    (hf : H.Feasible) {zStar : ℝ} (hζ : SparsePerturb r zStar) {z : ℝ} (hz : z∈Set.Icc 0 zStar)
    (σ : UnitaryIrrep H.stabilizer) (hσ : σ.dimension≠1)
    (ha : ¬ (1+c G.size)*Real.log σ.dimension ≤ e G.size*h*Real.log G.size-H.cost)
    (hF : Real.log σ.dimension < (G.size:ℝ)^(1-a/4)) :
    schattenMoment SparseScalar.q (H.conditionalAverage hf z σ) ≤
      Real.exp (-c G.size*Real.log σ.dimension+e G.size*h*Real.log G.size-H.cost) := by
  let ρ := σ.pullback H.stabilizerFreeEquiv.symm
  obtain ⟨k,t,hkt,ht,hD,hkM,⟨L⟩⟩ := exists_level ρ
  have hΩ : Fintype.card (H.FreeAt 0)≤G.size := by rw [H.card_freeAt]; exact Nat.sub_le _ _
  have hks := hkM.trans hΩ
  have hlogs := level_log_bounds ρ G.size_pos hΩ hkt ht hD
  change Real.log σ.dimension≤k*Real.log G.size ∧ (k:ℝ)≤4*Real.log σ.dimension at hlogs
  have hk : 1≤k := by
    by_contra hh
    have he : k=0 := by omega
    rw [he,pow_zero] at hD
    have hdim : σ.dimension=1 := by have hh0:=σ.positive; change σ.dimension≤1 at hD; omega
    exact hσ hdim
  have hL := (scale_coefficients hr G hG).1
  have hc := (scale_coefficients hr G hG).2.1
  have hc1 : c G.size≤1 := hc.trans (by norm_num [c0,a])
  have hF0 : 0≤Real.log σ.dimension := Real.log_nonneg (by exact_mod_cast σ.positive)
  have hallow := H.allowance_lower hr hG
  have hn := lt_of_not_ge ha
  have hhh : (h:ℝ)*Real.log G.size ≤ K0*Real.log σ.dimension := by
    have hm := mul_le_mul_of_nonneg_right hc1 hF0
    norm_num [e0,a,K0] at hallow ⊢
    nlinarith
  have hh : (h:ℝ)≤K0*k := by
    have hm := mul_le_mul_of_nonneg_left hlogs.1 (by norm_num [K0] : 0≤K0)
    exact (mul_le_mul_iff_right₀ hL).mp (by nlinarith)
  have hsp : ((h+k:ℕ):ℝ)≤(G.size:ℝ)^(1-theta) := by
    have hh0 := (Nat.cast_nonneg h : (0:ℝ)≤h)
    have hhle : (h:ℝ)≤K0*Real.log σ.dimension := by nlinarith [hS.one]
    have hsum : ((h+k:ℕ):ℝ)≤(100004:ℝ)*Real.log σ.dimension := by
      push_cast
      norm_num [K0] at hhle
      linarith [hlogs.2]
    apply hsum.trans
    apply (mul_le_mul_of_nonneg_left hF.le (by norm_num : (0:ℝ)≤100004)).trans
    simpa only [theta] using hS.sparse
  have hnorm := H.level_sparse_norm hrS hG hf hζ hz hk hks hh hsp ρ L
  rw [show ρ=σ.pullback H.stabilizerFreeEquiv.symm from rfl,H.conditionalAverage_free_cancel] at hnorm
  let : NeZero σ.dimension := ⟨σ.positive.ne'⟩
  have hp := pow_le_pow_left₀ (norm_nonneg (H.conditionalAverage hf z σ)) hnorm (2*SparseScalar.q)
  calc
    _ ≤ (σ.dimension:ℝ)*‖H.conditionalAverage hf z σ‖^(2*SparseScalar.q) := trace_moment_le _ _
    _ ≤ (σ.dimension:ℝ)*((G.size:ℝ)^(-rho*k))^(2*SparseScalar.q) :=
      mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg _)
    _ = Real.exp (Real.log σ.dimension-4*k*Real.log G.size) := by
      rw [rpow_exp _ _ (by exact_mod_cast G.size_pos),←Real.exp_nat_mul]
      nth_rw 1 [←Real.exp_log (by exact_mod_cast σ.positive : (0:ℝ)<σ.dimension)]
      rw [←Real.exp_add]
      congr 1
      norm_num [SparseScalar.q,rho]
      ring
    _ ≤ Real.exp (-3*Real.log σ.dimension) := Real.exp_le_exp.mpr (by nlinarith [hlogs.1])
    _ ≤ _ := Real.exp_le_exp.mpr (by
      have hm := mul_le_mul_of_nonneg_right hc1 hF0
      have ha0 := H.allowance_nonneg hr hG
      linarith)
end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps
/-- Real exponential version of the exact conditional main estimate, used only
as the induction predicate; its equivalence to logMoment includes zero moments. -/
def MomentBound (G : Grid) (q : ℕ) (z : ℝ) : Prop :=
  ∀ (h : ℕ) (H : G.Holes h) (hf : H.Feasible) (σ : UnitaryIrrep H.stabilizer),
    schattenMoment q (H.conditionalAverage hf z σ) ≤
      Real.exp (-c G.size*Real.log σ.dimension+e G.size*h*Real.log G.size-H.cost)
noncomputable def cHat (s : ℕ) : ℝ := c s+1/(20*Real.sqrt (Real.log s))
noncomputable def eHat (s : ℕ) : ℝ := e s-1/(20*Real.sqrt (Real.log s))
end CoordinateSweeps
namespace CoordinateSweeps.Grid.Holes
open ScalarInduction YoungCorner
variable {A B : Grid} {r h q : ℕ} (H : (concat A B).Holes h)
theorem hook_auxiliary (hr : ScaleLarge r) (hA : A.Allowed r) (hB : B.Allowed r)
    (hAB : A.b≤B.b) (hBA : B.b≤2*A.b) (hq : 1≤q)
    (hS : MainSizeReady q (concat A B).size)
    (z : ℝ) (hIA : MomentBound A q z) (hIB : MomentBound B q z)
    (hf : H.Feasible) (σ : UnitaryIrrep H.stabilizer)
    (p : ℕ) (hp : 0<p) (hpp : (p:ℝ)≤((concat A B).size:ℝ)^a)
    (μ : YoungDiagram) (eB : H.FreeAt 0 ≃ Boxes μ)
    (hσ : hasShape μ (Equiv.refl _) (σ.pullback (H.boxesChart μ eB)).asRepresentation)
    (hhook : Hook μ p) :
    schattenMoment q (H.conditionalAverage hf z σ) ≤
      Real.exp (-cHat (concat A B).size*Real.log σ.dimension+
        eHat (concat A B).size*h*Real.log (concat A B).size-H.cost+
          ((concat A B).size:ℝ)^((9:ℝ)/10)) := by
  let G := concat A B
  let L := Real.log G.size
  let cStar := c0+(11/10:ℝ)/Real.sqrt L
  let eStar := e0-(11/10:ℝ)/Real.sqrt L
  have hG : G.Allowed r := (concat_allowed A B r).mpr ⟨hA,hB⟩
  have hL : 0<L := (scale_coefficients hr G hG).1
  have hLA := (scale_coefficients hr A hA).1
  have hLB := (scale_coefficients hr B hB).1
  have hlogs := balanced_logs hA hB hAB hBA
  have hcsA : cStar≤c A.size ∧ e A.size≤eStar := improved_coefficients hL hLA hlogs.2.1
  have hcsB : cStar≤c B.size ∧ e B.size≤eStar := improved_coefficients hL hLB hlogs.2.2.2
  have hc : 0≤cStar := by
    dsimp [cStar]
    have hc0 : 0≤c0 := by norm_num [c0,a]
    positivity
  have hc2 : cStar≤2*c0 := hcsA.1.trans (scale_coefficients hr A hA).2.1
  have hcq : cStar≤q := hc2.trans ((by norm_num [c0,a] : 2*c0≤1).trans (by exact_mod_cast hq))
  have hR : ∀ y : B.Slot, ∀ τ : UnitaryIrrep (H.rowHoles y).stabilizer,
      schattenMoment q ((H.rowHoles y).conditionalAverage (H.rowHoles y).feasible_of_disjoint z τ) ≤
        Real.exp (-cStar*Real.log τ.dimension+eStar*H.rowCount y*Real.log A.size-(H.rowHoles y).cost) := by
    intro y τ
    apply (hIA _ _ _ τ).trans (Real.exp_le_exp.mpr ?_)
    have hF := Real.log_nonneg (show (1:ℝ)≤τ.dimension by exact_mod_cast τ.positive)
    have hc' := mul_le_mul_of_nonneg_right hcsA.1 hF
    have he' := mul_le_mul_of_nonneg_right hcsA.2
      (show 0≤(H.rowCount y:ℝ)*Real.log A.size by positivity)
    nlinarith
  have hC : ∀ x : A.Slot, ∀ τ : UnitaryIrrep (H.columnHoles x).stabilizer,
      schattenMoment q ((H.columnHoles x).conditionalAverage (H.columnHoles x).feasible_of_disjoint z τ) ≤
        Real.exp (-cStar*Real.log τ.dimension+eStar*H.columnCount x*Real.log B.size-(H.columnHoles x).cost) := by
    intro x τ
    apply (hIB _ _ _ τ).trans (Real.exp_le_exp.mpr ?_)
    have hF := Real.log_nonneg (show (1:ℝ)≤τ.dimension by exact_mod_cast τ.positive)
    have hc' := mul_le_mul_of_nonneg_right hcsB.1 hF
    have he' := mul_le_mul_of_nonneg_right hcsB.2
      (show 0≤(H.columnCount x:ℝ)*Real.log B.size by positivity)
    nlinarith
  have hs1 : (1:ℝ)<G.size := (Real.log_pos_iff (by exact_mod_cast G.size_pos.le)).mp hL
  have hpS : p≤G.size := by
    have hx : (G.size:ℝ)^a≤G.size := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hs1.le (show a≤1 by norm_num [a])
    exact_mod_cast hpp.trans hx
  have hAS : A.size≤G.size := by dsimp [G]; rw [concat_size]; nlinarith [A.size_pos,B.size_pos]
  have hBS : B.size≤G.size := by dsimp [G]; rw [concat_size]; nlinarith [A.size_pos,B.size_pos]
  have ht := H.actual_hook_bound p hp hf z q (by omega) cStar eStar hc hcq G.size hpS hAS hBS σ hR hC μ eB hσ hhook
  have hsizes := balanced_sizes hA hB hAB hBA
  have hErr := hook_error_bound hs1 q A.size B.size p cStar hc hc2 hsizes.2.1 hsizes.2.2.2 hpp
  have hroot : 2/e0≤Real.sqrt L := (Real.le_sqrt (by norm_num [e0,a]) hL.le).mpr
    (hr.2.1.trans (G.log_size_lower_one hG))
  have hgap := hook_strengthening hL hroot hc2
  have hcompare := hook_comparison (F:=Real.log σ.dimension) (h:=(h:ℝ)) (E:=
    (((2*q+1:ℕ):ℝ)*((A.size+B.size)*((2*p)*(2*p)):ℕ)+cStar*((A.size+B.size)*(41*p^2):ℕ))*Real.log (G.size+1:ℕ))
    hL (Real.log_nonneg (by exact_mod_cast σ.positive)) (Nat.cast_nonneg _) hgap.1 hgap.2
  have hlogsum : Real.log A.size+Real.log B.size=L := by
    dsimp [L,G]
    rw [concat_size,Nat.cast_mul,Real.log_mul (by exact_mod_cast A.size_pos.ne') (by exact_mod_cast B.size_pos.ne')]
  rw [hlogsum] at ht
  apply ht.trans (Real.exp_le_exp.mpr ?_)
  have hES : _ ≤ (G.size:ℝ)^((9:ℝ)/10) := hErr.trans hS.hook
  simp only [Nat.cast_add,Nat.cast_one,Nat.cast_mul] at hcompare hES ⊢
  dsimp [cHat,eHat,c,e]
  change _ ≤ -(c0+1/Real.sqrt L+1/(20*Real.sqrt L))*Real.log σ.dimension+
    (e0-1/Real.sqrt L-1/(20*Real.sqrt L))*h*L-H.cost+(G.size:ℝ)^((9:ℝ)/10)
  dsimp [cStar,eStar] at *
  nlinarith
end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.YoungCorner
lemma log_factorial_lower (k : ℕ) (hk : 0<k) :
    (k:ℝ)*Real.log k-k ≤ Real.log (k.factorial:ℝ) := by
  have hs := Stirling.le_log_factorial_stirling hk.ne'
  have hk1 : (1:ℝ)≤k := by exact_mod_cast hk
  have hl := Real.log_nonneg hk1
  have hp : 0≤Real.log (2*Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  linarith
lemma shape_finrank_pos (μ : YoungDiagram) :
    0 < Module.finrank ℂ (shapeSubrep μ (Equiv.refl _)).toSubmodule := by
  have : Nontrivial (shapeSubrep μ (Equiv.refl _)).toSubmodule :=
    by
      by_contra hn
      have : Subsingleton (shapeSubrep μ (Equiv.refl _)).toSubmodule := not_nontrivial_iff_subsingleton.mp hn
      apply bot_ne_top (α := Subrepresentation (shapeSubrep μ (Equiv.refl _)).toRepresentation)
      exact Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _)
  exact Module.finrank_pos
/-- The translated removed diagram has the entropy required in the large-k
branch, using the checked factorial/rank-count lower bound. -/
lemma removed_dimension_entropy (μ : YoungDiagram) (p s : ℕ)
    (hs : 0<s) (hM : Fintype.card (Boxes μ) ≤ s)
    (hfloor : (s:ℝ)^a ≤ p+1) (hL : 800 ≤ Real.log s)
    (hk : (s:ℝ)^(1-a/2) ≤ Fintype.card (Boxes (removedPart μ p))) :
    (a/4)*(Fintype.card (Boxes (removedPart μ p)):ℝ)*Real.log s ≤
      Real.log (Module.finrank ℂ (shapeSubrep (removedPart μ p) (Equiv.refl _)).toSubmodule) := by
  let k := Fintype.card (Boxes (removedPart μ p))
  let D := Module.finrank ℂ (shapeSubrep (removedPart μ p) (Equiv.refl _)).toSubmodule
  let L := 2*(Fintype.card (Boxes μ)/(p+1))
  have hs0 : (0:ℝ)<s := by exact_mod_cast hs
  have hk0 : 0<k := by
    have hh : (0:ℝ)<k := (Real.rpow_pos_of_pos hs0 _).trans_le hk
    exact_mod_cast hh
  have hD0 : 0<D := shape_finrank_pos _
  have hLp : 0<L := by
    obtain ⟨x⟩ := Fintype.card_pos_iff.mp hk0
    exact Nat.zero_le (x.val.1+x.val.2) |>.trans_lt (removedPart_rank_lt μ p x)
  have hL0 : (0:ℝ)<L := by exact_mod_cast hLp
  have hc := shape_dimension_entropy (removedPart μ p)
    (shapeSubrep (removedPart μ p) (Equiv.refl _)).toRepresentation
    (shapeSubrep_hasShape _ _) L (removedPart_rank_lt μ p)
  have hc' : (k.factorial:ℝ) ≤ (L:ℝ)^k*D := by exact_mod_cast hc
  have hlog := Real.log_le_log (by exact_mod_cast Nat.factorial_pos k : (0:ℝ)<k.factorial) hc'
  rw [Real.log_mul (by positivity : (L:ℝ)^k≠0) (by exact_mod_cast hD0.ne'),Real.log_pow] at hlog
  have hfac := log_factorial_lower k hk0
  have hLp' : (L:ℝ)*(p+1) ≤ 2*s := by
    have hh := Nat.div_mul_le_self (Fintype.card (Boxes μ)) (p+1)
    have hh' : (Fintype.card (Boxes μ)/(p+1))*(p+1) ≤ s := hh.trans hM
    dsimp [L]
    exact_mod_cast (show 2*(Fintype.card (Boxes μ)/(p+1))*(p+1)≤2*s by nlinarith [hh'])
  have hLupper : (L:ℝ) ≤ 2*(s:ℝ)^(1-a) := by
    have hh := mul_le_mul_of_nonneg_left hfloor hL0.le
    have hhs : (L:ℝ)*(s:ℝ)^a ≤ 2*s := hh.trans hLp'
    apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hs0 a)).mp
    calc
      _ ≤ 2*(s:ℝ) := hhs
      _ = 2*(s:ℝ)^(1-a)*(s:ℝ)^a := by rw [mul_assoc,←Real.rpow_add hs0]; norm_num
  have hLogL : Real.log L ≤ Real.log 2+(1-a)*Real.log s := by
    have hh := Real.log_le_log hL0 hLupper
    rw [Real.log_mul (by norm_num : (2:ℝ)≠0) (Real.rpow_pos_of_pos hs0 _).ne',Real.log_rpow hs0] at hh
    exact hh
  have hLogk : (1-a/2)*Real.log s ≤ Real.log k := by
    have hh := Real.log_le_log (Real.rpow_pos_of_pos hs0 (1-a/2)) hk
    simpa only [Real.log_rpow hs0] using hh
  have hl2 : Real.log 2≤1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith
  have hkR : (0:ℝ)≤k := Nat.cast_nonneg _
  have hh1 := mul_le_mul_of_nonneg_left hLogL hkR
  have hh2 := mul_le_mul_of_nonneg_left hLogk hkR
  have hh3 : (a/4)*Real.log s ≥ Real.log 2+1 := by norm_num [a] at *; linarith
  have hh4 := mul_le_mul_of_nonneg_left hh3 hkR
  change (a/4)*(k:ℝ)*Real.log s ≤ Real.log D
  nlinarith
end CoordinateSweeps.YoungCorner

namespace CoordinateSweeps.Grid.Holes
open YoungCorner ScalarInduction
variable {G : Grid} {h : ℕ} (H : G.Holes h)
lemma exists_initial_shape (σ : UnitaryIrrep H.stabilizer) :
    ∃ (μ : YoungDiagram) (eB : H.FreeAt 0 ≃ Boxes μ),
      hasShape μ (Equiv.refl _) (σ.pullback (H.boxesChart μ eB)).asRepresentation := by
  let τ := (σ.pullback H.stabilizerFreeEquiv.symm).asRepresentation
  obtain ⟨p,hp⟩ := exists_partitionShape τ
  refine ⟨diagramOfPartition p,partitionFilling p,?_⟩
  have hh : hasShape (V:=Fin σ.dimension → ℂ) (diagramOfPartition p)
      ((partitionFilling p).symm.trans (partitionFilling p))
      (τ.comp (partitionFilling p).symm.permCongrHom) :=
    (hasShape_reparam (diagramOfPartition p) (partitionFilling p).symm (partitionFilling p) τ).mpr hp
  change hasShape (V:=Fin σ.dimension → ℂ) (diagramOfPartition p) (Equiv.refl _)
    (τ.comp (partitionFilling p).symm.permCongrHom)
  simpa only [Equiv.symm_trans_self] using hh

lemma augmented_boxesChart (μ : YoungDiagram) (p : ℕ) (eB : H.FreeAt 0 ≃ Boxes μ)
    (x : H.Placement (k := Fintype.card (Boxes (removedPart μ p))))
    (ω₀ : {ω : G.Choices // H.Compatible ω}) :
    (H.augmented x ω₀).boxesChart (hookPart μ p) (H.augmentedRetainedEquiv μ p eB x ω₀).symm=
      H.augmentedRetainedChart μ p eB x ω₀ := by
  rfl
lemma retained_log_dimension (μ : YoungDiagram) (p : ℕ) (eB : H.FreeAt 0 ≃ Boxes μ)
    (σ : UnitaryIrrep H.stabilizer)
    (ρ : UnitaryIrrep (H.placementChart (H.removedPlacement μ p eB)).stabilizer)
    (hd : σ.dimension≤(Fintype.card (Boxes μ))^(Fintype.card (Boxes (removedPart μ p)))*ρ.dimension) :
    Real.log σ.dimension≤Real.log ρ.dimension+
      Fintype.card (Boxes (removedPart μ p))*Real.log G.size := by
  have hM : Fintype.card (Boxes μ)≤G.size := by
    rw [←Fintype.card_congr eB,H.card_freeAt]
    exact Nat.sub_le _ _
  have hh := hd.trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hM _))
  have hhR : (σ.dimension:ℝ)≤(G.size:ℝ)^(Fintype.card (Boxes (removedPart μ p)))*ρ.dimension := by exact_mod_cast hh
  have hlog := Real.log_le_log (by exact_mod_cast σ.positive : (0:ℝ)<σ.dimension) hhR
  have hs0 : (0:ℝ)<G.size := by exact_mod_cast G.size_pos
  rw [Real.log_mul (by positivity : (G.size:ℝ)^(Fintype.card (Boxes (removedPart μ p)))≠0)
    (by exact_mod_cast ρ.positive.ne'),Real.log_pow] at hlog
  linarith
end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.Grid.Holes
open YoungCorner ScalarInduction
variable {A B : Grid} {r h q : ℕ} (H : (concat A B).Holes h)
/-- Large-dimension branch of the exact main: actual retained constituent,
actual augmented paths, induced placement-cycle estimate, and absorbed entropy. -/
theorem conditional_large_main (hr : ScaleLarge r) (hA : A.Allowed r) (hB : B.Allowed r)
    (hAB : A.b≤B.b) (hBA : B.b≤2*A.b) (hq : 1≤q)
    (hS : MainSizeReady q (concat A B).size)
    (z : ℝ) (hz : 0≤z) (hz' : z<1)
    (hlo : ∀ j g, (1/2:ℝ)*FiniteLaw.uniform _ g≤lineLaw ((concat A B).bits j) z hz hz'.le g)
    (hhi : ∀ j g, lineLaw ((concat A B).bits j) z hz hz'.le g≤2*FiniteLaw.uniform _ g)
    (hIA : MomentBound A q z) (hIB : MomentBound B q z)
    (hf : H.Feasible) (σ : UnitaryIrrep H.stabilizer)
    (hF : ((concat A B).size:ℝ)^(1-a/4)≤Real.log σ.dimension) :
    schattenMoment q (H.conditionalAverage hf z σ)≤
      Real.exp (-c (concat A B).size*Real.log σ.dimension+
        e (concat A B).size*h*Real.log (concat A B).size-H.cost) := by
  let G := concat A B
  let p := ⌊(G.size:ℝ)^a⌋₊
  let L := Real.log G.size
  obtain ⟨μ,eB,hσ⟩ := H.exists_initial_shape σ
  obtain ⟨ρ,hρ,hm,hd⟩ := H.exists_retained_irrep μ p eB σ hσ
  let k := Fintype.card (Boxes (removedPart μ p))
  let D := Module.finrank ℂ (shapeSubrep (removedPart μ p) (Equiv.refl _)).toSubmodule
  have hG : G.Allowed r := (concat_allowed A B r).mpr ⟨hA,hB⟩
  have hcoeff := scale_coefficients hr G hG
  have hL : 0<L := hcoeff.1
  have hs : (1:ℝ)<G.size := (Real.log_pos_iff (by exact_mod_cast G.size_pos.le)).mp hL
  have hs0 : (0:ℝ)<G.size := by exact_mod_cast G.size_pos
  have hp : 0<p := by
    change 1≤⌊(G.size:ℝ)^a⌋₊
    apply (Nat.one_le_floor_iff _).mpr
    exact Real.one_le_rpow hs.le (by norm_num [a])
  have hpp : (p:ℝ)≤(G.size:ℝ)^a := Nat.floor_le (Real.rpow_nonneg hs0.le _)
  have hfloor : (G.size:ℝ)^a≤p+1 := (Nat.lt_floor_add_one _).le
  let budget := -cHat G.size*Real.log ρ.dimension+eHat G.size*(h+k)*L+(G.size:ℝ)^((9:ℝ)/10)
  have hT : ∀ (x : H.Placement (k:=k)) (ω₀ : {ω : G.Choices // H.Compatible ω}),
      schattenMoment q ((H.augmented x ω₀).conditionalAverage (H.augmented_feasible x ω₀) z
        (H.augmentedIrrep (H.removedPlacement μ p eB) x ω₀ ρ))≤Real.exp (budget-(H.augmented x ω₀).cost) := by
    intro x ω₀
    have hsH := H.augmented_hasShape μ p eB ρ hρ x ω₀
    rw [←H.augmented_boxesChart] at hsH
    have hh := (H.augmented x ω₀).hook_auxiliary hr hA hB hAB hBA hq hS z hIA hIB
      (H.augmented_feasible x ω₀) (H.augmentedIrrep (H.removedPlacement μ p eB) x ω₀ ρ)
      p hp hpp (hookPart μ p) (H.augmentedRetainedEquiv μ p eB x ω₀).symm hsH (hookPart_property μ p)
    apply hh.trans_eq
    congr 1
    change -cHat (concat A B).size*Real.log ρ.dimension+
      eHat (concat A B).size*((h+k:ℕ):ℝ)*Real.log (concat A B).size-
      (H.augmented x ω₀).cost+((concat A B).size:ℝ)^((9:ℝ)/10)=budget-(H.augmented x ω₀).cost
    dsimp [budget,L,k,G]
    push_cast
    ring
  have hind := H.actual_induced_endgame hf (H.removedPlacement μ p eB) ρ σ hz hz' hlo hhi q (by omega) budget hT
  have hMoment0 := H.conditionalMoment_nonneg hf z σ q
  have hD0 : 0<D := shape_finrank_pos _
  have hD0R : (0:ℝ)<D := by exact_mod_cast hD0
  have hDT : (D:ℝ)*schattenMoment q (H.conditionalAverage hf z σ)≤Real.exp (budget-H.cost+Real.log 4*k*G.b) :=
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hm) hMoment0).trans hind
  have ht : schattenMoment q (H.conditionalAverage hf z σ)≤
      Real.exp (budget-H.cost+Real.log 4*k*G.b-Real.log D) := by
    rw [Real.exp_sub,Real.exp_log hD0R]
    exact (le_div_iff₀ hD0R).mpr (by simpa only [mul_comm] using hDT)
  have hD := H.retained_log_dimension μ p eB σ ρ hd
  have hM : Fintype.card (Boxes μ)≤G.size := by
    rw [←Fintype.card_congr eB,H.card_freeAt]
    exact Nat.sub_le _ _
  have h800 : 800≤Real.log G.size := by
    have hh := hr.2.1.trans (G.log_size_lower_one hG)
    norm_num [e0,a] at hh
    linarith
  have hEnt : (G.size:ℝ)^(1-a/2)≤k → (a/4)*(k:ℝ)*L≤Real.log D := by
    intro hh
    exact removed_dimension_entropy μ p G.size G.size_pos hM hfloor h800 hh
  have hcost := removed_cost_bound hs (Nat.cast_nonneg k) (Nat.cast_nonneg G.b) hcoeff.2.2.2 hF
    (Real.log_nonneg (by exact_mod_cast hD0 : (1:ℝ)≤D)) hS hEnt
  have hscalar := removed_endgame L (Real.log σ.dimension) (Real.log ρ.dimension) (Real.log D)
    k h G.b H.cost G.size ((G.size:ℝ)^((9:ℝ)/10)) hL
    (Real.log_nonneg (by exact_mod_cast σ.positive)) (Nat.cast_nonneg _) (Nat.cast_nonneg _) hD
    (Real.sqrt_pos.mpr hL) hcost
  apply ht.trans (Real.exp_le_exp.mpr ?_)
  simpa only [budget,cHat,eHat,c,e,L] using hscalar
end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps
open Filter
lemma eventually_scaleLarge : ∀ᶠ r : ℕ in atTop, ScaleLarge r := by
  obtain ⟨r₀,hr₀⟩ := exists_scaleLarge
  filter_upwards [eventually_ge_atTop r₀] with r hr
  have hh : (r₀:ℝ)*Real.log 2 ≤ (r:ℝ)*Real.log 2 :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hr) (Real.log_nonneg (by norm_num))
  exact ⟨hr₀.1.trans hr,hr₀.2.1.trans hh,hr₀.2.2.trans hh⟩
lemma exists_main_scale : ∃ r : ℕ, ScaleLarge r ∧ SparseScalar.ScaleReady r ∧
    ∀ G : Grid, G.Allowed r → ScalarInduction.MainSizeReady SparseScalar.q G.size := by
  obtain ⟨S,hS⟩ := eventually_atTop.mp (ScalarInduction.eventually_mainSizeReady SparseScalar.q)
  have hp : Tendsto (fun r : ℕ => (2:ℝ)^r) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hall : ∀ᶠ r : ℕ in atTop, ScaleLarge r ∧ SparseScalar.ScaleReady r ∧ S≤(2:ℝ)^r := by
    filter_upwards [eventually_scaleLarge,SparseScalar.eventually_scaleReady,
      hp.eventually (eventually_ge_atTop S)] with r h1 h2 h3
    exact ⟨h1,h2,h3⟩
  obtain ⟨r,hr,hs,ht⟩ := hall.exists
  exact ⟨r,hr,hs,fun G hG => hS G.size (ht.trans (G.pow_r_le_size hG))⟩

/-- Strong induction on the literal ordered coordinate count; every child is
an actual conditioned row/column grid, not a surrogate representation law. -/
theorem all_grid_moment {r : ℕ} (hr : ScaleLarge r) (hrS : SparseScalar.ScaleReady r)
    (hS : ∀ G : Grid, G.Allowed r → ScalarInduction.MainSizeReady SparseScalar.q G.size)
    {zStar : ℝ} (hζ : SparsePerturb r zStar) {z : ℝ} (hz : z∈Set.Icc 0 zStar) :
    ∀ G : Grid, G.Allowed r → MomentBound G SparseScalar.q z := by
  have hzB : z≤baseZeta r := hz.2.trans hζ.2.1
  have hz1 : z<1 := lt_of_le_of_lt (hzB.trans (baseZeta_le_half r)) (by norm_num)
  have hq : 1≤SparseScalar.q := by norm_num [SparseScalar.q]
  have aux : ∀ n : ℕ, ∀ G : Grid, G.b=n → G.Allowed r → MomentBound G SparseScalar.q z := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro G hb hG h H hf σ
      have hnonneg := H.conditionalMoment_nonneg hf z σ SparseScalar.q
      by_cases hone : G.b=1
      · exact moment_le_exp_of_logMoment_le hnonneg
          (Grid.conditional_main_b_one hr G hone hG H hf hz.1 hzB σ hq)
      by_cases hdim : σ.dimension=1
      · exact moment_le_exp_of_logMoment_le hnonneg
          (H.conditional_dimension_one hr hG hf hz.1 hz1 σ hdim SparseScalar.q)
      by_cases haut : (1+c G.size)*Real.log σ.dimension ≤ e G.size*h*Real.log G.size-H.cost
      · exact moment_le_exp_of_logMoment_le hnonneg
          (H.conditional_automatic hf hz.1 hz1 σ SparseScalar.q haut)
      by_cases hF : Real.log σ.dimension < (G.size:ℝ)^(1-a/4)
      · exact H.conditional_sparse_main hr hrS hG (hS G hG) hf hζ hz σ hdim haut hF
      have hlarge : (G.size:ℝ)^(1-a/4)≤Real.log σ.dimension := le_of_not_gt hF
      have hb2 : 2≤G.b := by have hh:=G.positive; omega
      obtain ⟨A,B,hAB,hA,hB,hab,hba⟩ := G.exists_half_concat hb2
      have hallowed : A.Allowed r ∧ B.Allowed r :=
        (Grid.concat_allowed A B r).mp (by simpa only [hAB] using hG)
      have hIA : MomentBound A SparseScalar.q z := ih A.b (by omega) A rfl hallowed.1
      have hIB : MomentBound B SparseScalar.q z := ih B.b (by omega) B rfl hallowed.2
      subst G
      exact H.conditional_large_main hr hallowed.1 hallowed.2 hab hba hq
        (hS _ hG) z hz.1 hz1
        (fun j g => (lineLaw_base_bounds (hG j).2 hz.1 hzB g).1)
        (fun j g => (lineLaw_base_bounds (hG j).2 hz.1 hzB g).2)
        hIA hIB hf σ hlarge
  exact fun G hG => aux G.b G rfl hG

/-- Manuscript03 thm:conditional / ac:main, with c₀=e₀=a/100,
a=1/100, natural logarithms, unnormalized integer Schatten moments,
all feasible disjoint paths (including none and all), and log(0)=−∞. -/
theorem conditional_main : ConditionalMain := by
  obtain ⟨r,hr,hrS,hS⟩ := exists_main_scale
  obtain ⟨zStar,hζ⟩ := exists_sparsePerturb r
  have hq : 1≤SparseScalar.q := by norm_num [SparseScalar.q]
  refine ⟨r,SparseScalar.q,zStar,hr.1,hq,hζ.1,hζ.2.1.trans (baseZeta_le_half r),?_⟩
  intro G hG h H hf z hz σ
  exact logMoment_le_of_moment_le_exp (H.conditionalMoment_nonneg hf z σ SparseScalar.q)
    (all_grid_moment hr hrS hS hζ hz G hG h H hf σ)
end CoordinateSweeps

end OAI
