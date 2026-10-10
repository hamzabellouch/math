import OAI.Geometry.ConjugatePoints.Gluing
import OAI.Geometry.ConjugatePoints.Continuation

namespace OAI

noncomputable section

/-!
# Fundamental-group relations and nontrivial fiber classes.
-/

section

open Matrix Set Pointwise
open scoped MatrixGroups UpperHalfPlane
namespace ThreeManifold.HyperbolicCore

lemma phi_action (z : ℍ) : ((phi • z : ℍ) : ℂ) = ((z:ℂ)+1)/((z:ℂ)+2) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [phi]
lemma psi_action (z : ℍ) : ((psi • z : ℍ) : ℂ) = ((z:ℂ)-1)/(2-(z:ℂ)) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [psi, sub_eq_add_neg, add_comm]
def phiInv : SL(2,ℤ) := ⟨!![2,-1;-1,1], by norm_num [Matrix.det_fin_two]⟩
def psiInv : SL(2,ℤ) := ⟨!![2,1;1,1], by norm_num [Matrix.det_fin_two]⟩
lemma phi_inv_eq : phi⁻¹ = phiInv := by
  apply Subtype.ext
  change Matrix.adjugate (phi : Matrix (Fin 2) (Fin 2) ℤ) = _
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [phi, phiInv, Matrix.adjugate_fin_two]
lemma psi_inv_eq : psi⁻¹ = psiInv := by
  apply Subtype.ext
  change Matrix.adjugate (psi : Matrix (Fin 2) (Fin 2) ℤ) = _
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [psi, psiInv, Matrix.adjugate_fin_two]
lemma phi_inv_action (z : ℍ) : ((phi⁻¹ • z : ℍ) : ℂ) = (2*(z:ℂ)-1)/(1-(z:ℂ)) := by
  rw [phi_inv_eq, UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [phiInv, sub_eq_add_neg, add_comm]
lemma psi_inv_action (z : ℍ) : ((psi⁻¹ • z : ℍ) : ℂ) = (2*(z:ℂ)+1)/((z:ℂ)+1) := by
  rw [psi_inv_eq, UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [psiInv]

lemma phi_maps_right (z : ℍ) (hz : -1 < z.re) :
    Complex.normSq ((phi • z : ℍ) : ℂ) < (phi • z : ℍ).re := by
  change Complex.normSq ((phi • z : ℍ) : ℂ) < Complex.re ((phi • z : ℍ) : ℂ)
  rw [phi_action, Complex.normSq_div, Complex.div_re, ← add_div]
  have hd : 0 < Complex.normSq ((z:ℂ)+2) := by
    apply Complex.normSq_pos.mpr
    intro he
    have hi := congrArg Complex.im he
    norm_num at hi
    exact z.im_ne_zero hi
  apply (div_lt_div_iff_of_pos_right hd).2
  norm_num [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.one_re,
    Complex.one_im, Complex.natCast_re, Complex.natCast_im, add_zero, UpperHalfPlane.coe_re,
    UpperHalfPlane.coe_im]
  nlinarith

lemma psi_maps_left (z : ℍ) (hz : z.re < 1) :
    Complex.normSq ((psi • z : ℍ) : ℂ) < -(psi • z : ℍ).re := by
  change Complex.normSq ((psi • z : ℍ) : ℂ) < -Complex.re ((psi • z : ℍ) : ℂ)
  rw [psi_action, Complex.normSq_div, Complex.div_re, ← add_div, ← neg_div]
  have hd : 0 < Complex.normSq (2-(z:ℂ)) := by
    apply Complex.normSq_pos.mpr
    intro he
    have hi := congrArg Complex.im he
    norm_num at hi
    exact z.im_ne_zero hi
  apply (div_lt_div_iff_of_pos_right hd).2
  norm_num [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
    Complex.one_im, Complex.natCast_re, Complex.natCast_im, sub_zero, zero_sub,
    UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  nlinarith

lemma phi_inv_maps_outside (z : ℍ) (hz : z.re ≤ Complex.normSq (z:ℂ)) :
    (phi⁻¹ • z : ℍ).re ≤ -1 := by
  change Complex.re ((phi⁻¹ • z : ℍ) : ℂ) ≤ -1
  rw [phi_inv_action, Complex.div_re, ← add_div]
  have hd : 0 < Complex.normSq (1-(z:ℂ)) := by
    apply Complex.normSq_pos.mpr
    intro he
    have hi := congrArg Complex.im he
    simp only [Complex.sub_im, Complex.one_im, zero_sub, Complex.zero_im,
      UpperHalfPlane.coe_im, neg_eq_zero] at hi
    exact z.im_ne_zero hi
  apply (div_le_iff₀ hd).2
  norm_num [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.one_re, Complex.one_im, Complex.natCast_re, Complex.natCast_im,
    zero_mul, mul_zero, sub_zero, zero_sub, add_zero, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at hz ⊢
  nlinarith

lemma psi_inv_maps_outside (z : ℍ) (hz : -z.re ≤ Complex.normSq (z:ℂ)) :
    1 ≤ (psi⁻¹ • z : ℍ).re := by
  change 1 ≤ Complex.re ((psi⁻¹ • z : ℍ) : ℂ)
  rw [psi_inv_action, Complex.div_re, ← add_div]
  have hd : 0 < Complex.normSq ((z:ℂ)+1) := by
    apply Complex.normSq_pos.mpr
    intro he
    have hi := congrArg Complex.im he
    simp only [Complex.add_im, Complex.one_im, add_zero, Complex.zero_im,
      UpperHalfPlane.coe_im] at hi
    exact z.im_ne_zero hi
  apply (le_div_iff₀ hd).2
  norm_num [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.one_re, Complex.one_im, Complex.natCast_re, Complex.natCast_im,
    zero_mul, mul_zero, sub_zero, zero_sub, add_zero, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at hz ⊢
  nlinarith

def pairingGenerator : Bool → SL(2,ℤ) | false => phi | true => psi
def pairingX : Bool → Set ℍ
  | false => {z | Complex.normSq (z:ℂ) < z.re}
  | true => {z | Complex.normSq (z:ℂ) < -z.re}
def pairingY : Bool → Set ℍ
  | false => {z | z.re ≤ -1}
  | true => {z | 1 ≤ z.re}

lemma pairingX_nonempty (i : Bool) : (pairingX i).Nonempty := by
  cases i
  · refine ⟨⟨(1/2:ℂ)+(1/4:ℂ)*Complex.I, by norm_num⟩, ?_⟩
    change Complex.normSq ((1/2:ℂ)+(1/4:ℂ)*Complex.I) < _
    norm_num [Complex.normSq_apply]
  · refine ⟨⟨(-1/2:ℂ)+(1/4:ℂ)*Complex.I, by norm_num⟩, ?_⟩
    change Complex.normSq ((-1/2:ℂ)+(1/4:ℂ)*Complex.I) < _
    norm_num [Complex.normSq_apply]

lemma pairingX_disjoint : Pairwise (fun i j => Disjoint (pairingX i) (pairingX j)) := by
  intro i j hij
  cases i <;> cases j
  · exact (hij rfl).elim
  · rw [Set.disjoint_left]
    intro z hz hw
    change Complex.normSq (z:ℂ) < z.re at hz
    change Complex.normSq (z:ℂ) < -z.re at hw
    nlinarith [Complex.normSq_nonneg (z:ℂ)]
  · exact (by
      rw [Set.disjoint_left]
      intro z hz hw
      change Complex.normSq (z:ℂ) < -z.re at hz
      change Complex.normSq (z:ℂ) < z.re at hw
      nlinarith [Complex.normSq_nonneg (z:ℂ)])
  · exact (hij rfl).elim
lemma pairingY_disjoint : Pairwise (fun i j => Disjoint (pairingY i) (pairingY j)) := by
  intro i j hij
  cases i <;> cases j <;> simp_all [pairingY, Set.disjoint_left] <;> intro z hz <;> linarith
lemma pairingXY_disjoint (i j : Bool) : Disjoint (pairingX i) (pairingY j) := by
  rw [Set.disjoint_left]
  intro z hz hw
  cases i <;> cases j <;>
    change _ at hz hw <;>
    simp only [pairingX, pairingY, Set.mem_ofPred_eq, Complex.normSq_apply,
      UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at hz hw <;> nlinarith [sq_nonneg z.im]
lemma pairing_maps_X (i : Bool) : pairingGenerator i • (pairingY i)ᶜ ⊆ pairingX i := by
  rintro _ ⟨z,hz,rfl⟩
  cases i
  · exact phi_maps_right z (lt_of_not_ge hz)
  · exact psi_maps_left z (lt_of_not_ge hz)
lemma pairing_maps_Y (i : Bool) : (pairingGenerator i)⁻¹ • (pairingX i)ᶜ ⊆ pairingY i := by
  rintro _ ⟨z,hz,rfl⟩
  cases i
  · exact phi_inv_maps_outside z (le_of_not_gt hz)
  · exact psi_inv_maps_outside z (le_of_not_gt hz)

theorem pairing_free : Function.Injective (FreeGroup.lift pairingGenerator) :=
  FreeGroup.injective_lift_of_ping_pong pairingGenerator pairingX pairingY
    pairingX_nonempty pairingX_disjoint pairingY_disjoint pairingXY_disjoint
    pairing_maps_X pairing_maps_Y

lemma pairingGenerator_mem (i : Bool) : pairingGenerator i ∈ Γ := by
  cases i
  · exact phi_mem
  · exact psi_mem

def effectiveGenerator (i : Bool) : effective := effect ⟨pairingGenerator i,pairingGenerator_mem i⟩
lemma effectiveGenerator_smul (i : Bool) (z : ℍ) :
    effectiveGenerator i • z = pairingGenerator i • z := rfl
lemma effectiveGenerator_inv_smul (i : Bool) (z : ℍ) :
    (effectiveGenerator i)⁻¹ • z = (pairingGenerator i)⁻¹ • z := rfl

theorem effective_pairing_free : Function.Injective (FreeGroup.lift effectiveGenerator) := by
  apply FreeGroup.injective_lift_of_ping_pong effectiveGenerator pairingX pairingY
    pairingX_nonempty pairingX_disjoint pairingY_disjoint pairingXY_disjoint
  · intro i
    rintro _ ⟨z,hz,rfl⟩
    change effectiveGenerator i • z ∈ pairingX i
    rw [effectiveGenerator_smul]
    exact pairing_maps_X i (Set.smul_mem_smul_set hz)
  · intro i
    rintro _ ⟨z,hz,rfl⟩
    change (effectiveGenerator i)⁻¹ • z ∈ pairingY i
    rw [effectiveGenerator_inv_smul]
    exact pairing_maps_Y i (Set.smul_mem_smul_set hz)

lemma effect_neg_one : effect ⟨-1,neg_one_mem⟩ = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  intro z
  change ((-1:SL(2,ℤ)) • z) = z
  simp

def permutationLift : FreeGroup Bool →* Equiv.Perm ℍ :=
  effective.subtype.comp (FreeGroup.lift effectiveGenerator)

lemma gamma_permutation_mem_range (g : SL(2,ℤ)) (hg : g ∈ Γ) :
    MulAction.toPermHom SL(2,ℤ) ℍ g ∈ permutationLift.range := by
  have hle : Γ ≤ permutationLift.range.comap (MulAction.toPermHom SL(2,ℤ) ℍ) := by
    apply (Subgroup.closure_le _).2
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · refine ⟨FreeGroup.of false, ?_⟩
      simp only [permutationLift,MonoidHom.comp_apply,FreeGroup.lift_apply_of]
      apply Equiv.ext
      intro z
      rfl
    · refine ⟨FreeGroup.of true, ?_⟩
      simp only [permutationLift,MonoidHom.comp_apply,FreeGroup.lift_apply_of]
      apply Equiv.ext
      intro z
      rfl
    · refine ⟨1, ?_⟩
      rw [map_one]
      apply Equiv.ext
      intro z
      change z = (-1:SL(2,ℤ)) • z
      simp
  exact hle hg

theorem effective_pairing_surjective : Function.Surjective (FreeGroup.lift effectiveGenerator) := by
  intro e
  obtain ⟨g,rfl⟩ := effect_surjective e
  obtain ⟨w,hw⟩ := gamma_permutation_mem_range g g.property
  exact ⟨w, Subtype.ext hw⟩

def effectiveFreeEquiv : FreeGroup Bool ≃* effective :=
  MulEquiv.ofBijective (FreeGroup.lift effectiveGenerator)
    ⟨effective_pairing_free,effective_pairing_surjective⟩

def surfaceFundamentalGroupEquiv (z : ℍ) :
    FundamentalGroup Surface (projection z) ≃* effectiveᵐᵒᵖ :=
  projection_cover.fundamentalGroupEquiv ⟨z,rfl⟩

end ThreeManifold.HyperbolicCore
end

section
open Set Filter Topology ModularGroup
open scoped UpperHalfPlane
namespace ThreeManifold.HyperbolicCore

def horoline (a t : ℝ) (ha : 0 < a) : ℍ := ⟨(6*t:ℂ) + a*Complex.I, by simpa using ha⟩
lemma horoline_continuous (a : ℝ) (ha : 0 < a) : Continuous (fun t => horoline a t ha) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun t : ℝ => ((6*t:ℂ) + a*Complex.I))
  fun_prop
lemma horoline_one (a : ℝ) (ha : 0 < a) : horoline a 1 ha = T^6 • horoline a 0 ha := by
  apply UpperHalfPlane.ext
  rw [show (T ^ (6:ℕ)) = T ^ (6:ℤ) by norm_cast, ModularGroup.coe_T_zpow_smul_eq]
  simp [horoline]
  ring

def boundaryPath (a : ℝ) (ha : 0 < a) : Path (projection (horoline a 0 ha)) (projection (horoline a 0 ha)) where
  toFun t := projection (horoline a t ha)
  continuous_toFun := projection_cover.continuous.comp ((horoline_continuous a ha).comp continuous_subtype_val)
  source' := rfl
  target' := by change projection (horoline a 1 ha) = _; rw [horoline_one,projection_smul _ T_six_mem]

def boundaryClass (a : ℝ) (ha : 0 < a) : FundamentalGroup Surface (projection (horoline a 0 ha)) :=
  FundamentalGroup.fromPath (.mk (boundaryPath a ha))

lemma boundaryClass_effect (a : ℝ) (ha : 0 < a) :
    surfaceFundamentalGroupEquiv (horoline a 0 ha) (boundaryClass a ha) =
      MulOpposite.op (effect ⟨T^6,T_six_mem⟩) := by
  change projection_cover.fundamentalGroupToMulOpposite ⟨horoline a 0 ha,rfl⟩
    (boundaryClass a ha) = MulOpposite.op (effect ⟨T^6,T_six_mem⟩)
  apply (projection_cover.fundamentalGroupToMulOpposite_apply_eq_Iff).2
  let hp := projection_cover.isCoveringMap
  have hl : (fun t : unitInterval => horoline a t ha) = hp.liftPath (boundaryPath a ha)
      (horoline a 0 ha) rfl := by
    apply (hp.eq_liftPath_iff rfl).2
    exact ⟨(horoline_continuous a ha).comp continuous_subtype_val,rfl,rfl⟩
  change T^6 • horoline a 0 ha = hp.liftPath (boundaryPath a ha) (horoline a 0 ha) rfl 1
  rw [← hl]; exact (horoline_one a ha).symm

lemma peripheral_effect : effect ⟨T^6,T_six_mem⟩ =
    (effectiveGenerator true)⁻¹*(effectiveGenerator false)⁻¹*
      effectiveGenerator true*effectiveGenerator false := by
  have hm : (⟨T^6,T_six_mem⟩ : Γ) = ⟨-1,neg_one_mem⟩ *
      ((⟨psi,psi_mem⟩ : Γ)⁻¹ * (⟨phi,phi_mem⟩ : Γ)⁻¹ * ⟨psi,psi_mem⟩ * ⟨phi,phi_mem⟩) := by
    apply Subtype.ext
    change T^6 = (-1)*(psi⁻¹*phi⁻¹*psi*phi)
    rw [peripheral_matrix]
    simp
  rw [hm,map_mul,effect_neg_one,one_mul]
  simp only [map_mul,map_inv,effectiveGenerator,pairingGenerator]

theorem boundaryClass_commutator (a : ℝ) (ha : 0 < a) :
    ∃ A B : FundamentalGroup Surface (projection (horoline a 0 ha)),
      boundaryClass a ha = A*B*A⁻¹*B⁻¹ := by
  let e := surfaceFundamentalGroupEquiv (horoline a 0 ha)
  refine ⟨e.symm (MulOpposite.op (effectiveGenerator false)),
    e.symm (MulOpposite.op (effectiveGenerator true)),?_⟩
  apply e.injective
  simp only [map_mul,map_inv,MulEquiv.apply_symm_apply]
  rw [boundaryClass_effect,peripheral_effect]
  simp only [MulOpposite.op_mul,MulOpposite.op_inv]
  group
end ThreeManifold.HyperbolicCore
end

section
open Set Topology
namespace ThreeManifold.LoopTopology
open Path.Homotopic
variable {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {x : X} {y : Y}
def pair (a : FundamentalGroup X x) (b : FundamentalGroup Y y) :
    FundamentalGroup (X×Y) (x,y) := prod a b
lemma pair_mul (a c : FundamentalGroup X x) (b d : FundamentalGroup Y y) :
    pair (a*c) (b*d) = pair a b * pair c d :=
  (comp_prod_eq_prod_comp c d a b).symm
lemma pair_one : pair (1 : FundamentalGroup X x) (1 : FundamentalGroup Y y) =
    (1 : FundamentalGroup (X×Y) (x,y)) := by
  change Path.Homotopic.Quotient.mk ((Path.refl x).prod (Path.refl y)) = Path.Homotopic.Quotient.mk (Path.refl (x,y))
  congr
lemma pair_commute (a : FundamentalGroup X x) (b : FundamentalGroup Y y) :
    Commute (pair a 1) (pair 1 b) := by
  change pair a 1 * pair 1 b = pair 1 b * pair a 1
  rw [← pair_mul,← pair_mul]; simp
lemma pair_split (a : FundamentalGroup X x) (b : FundamentalGroup Y y) :
    pair a b = pair a 1 * pair 1 b := by rw [← pair_mul]; simp

def leftHom (y : Y) : FundamentalGroup X x →* FundamentalGroup (X×Y) (x,y) where
  toFun a := pair a 1
  map_one' := pair_one
  map_mul' a b := by simpa using pair_mul a b (1 : FundamentalGroup Y y) 1

lemma map_trans (F : C(X,Y)) {x₀ x₁ x₂ : X}
    (p : Path.Homotopic.Quotient x₀ x₁) (q : Path.Homotopic.Quotient x₁ x₂) :
    (p.trans q).map F = (p.map F).trans (q.map F) := by
  induction p using Path.Homotopic.Quotient.ind with | mk p =>
  induction q using Path.Homotopic.Quotient.ind with | mk q =>
  exact congrArg Path.Homotopic.Quotient.mk (p.map_trans q F.continuous)

lemma fiber_null_transfer (F : C(X×Y,Z)) {x₀ x₁ : X} (p : Path x₀ x₁)
    (b : FundamentalGroup Y y) :
    FundamentalGroup.map F (x₀,y) (pair 1 b) = 1 ↔
      FundamentalGroup.map F (x₁,y) (pair 1 b) = 1 := by
  let q : Path.Homotopic.Quotient (x₀,y) (x₁,y) := prod (Path.Homotopic.Quotient.mk p) (.refl y)
  have h : (pair (1 : FundamentalGroup X x₀) b).trans q =
      q.trans (pair (1 : FundamentalGroup X x₁) b) := by
    change (prod (.refl x₀) b).trans (prod (Path.Homotopic.Quotient.mk p) (.refl y)) =
      (prod (Path.Homotopic.Quotient.mk p) (.refl y)).trans (prod (.refl x₁) b)
    rw [comp_prod_eq_prod_comp,comp_prod_eq_prod_comp]
    simp
  have hm := congrArg (fun k : Path.Homotopic.Quotient (x₀,y) (x₁,y) => k.map F) h
  simp only [map_trans] at hm
  change (FundamentalGroup.map F (x₀,y) (pair 1 b)).trans (q.map F) =
    (q.map F).trans (FundamentalGroup.map F (x₁,y) (pair 1 b)) at hm
  constructor
  · intro h0
    rw [h0] at hm
    have he := congrArg (fun k => (q.map F).symm.trans k) hm
    simpa only [FundamentalGroup.one_def,Path.Homotopic.Quotient.refl_trans,← Path.Homotopic.Quotient.trans_assoc,
      Path.Homotopic.Quotient.symm_trans,Path.Homotopic.Quotient.refl_trans] using he.symm
  · intro h1
    rw [h1] at hm
    have he := congrArg (fun k => k.trans (q.map F).symm) hm
    simpa only [FundamentalGroup.one_def,Path.Homotopic.Quotient.trans_refl,Path.Homotopic.Quotient.trans_assoc,
      Path.Homotopic.Quotient.trans_symm,Path.Homotopic.Quotient.trans_refl] using he
lemma loop_cast_eq_one_iff {x y : X} (h : y = x) (q : FundamentalGroup X x) :
    Path.Homotopic.Quotient.cast q h h = (1 : FundamentalGroup X y) ↔ q = (1 : FundamentalGroup X x) := by
  subst y
  rw [Path.Homotopic.Quotient.cast_rfl_rfl]
lemma mapOfEq_eq_one_iff (F : C(X,Y)) {x : X} {y : Y} (h : F x = y)
    (q : FundamentalGroup X x) :
    FundamentalGroup.mapOfEq F h q = 1 ↔ FundamentalGroup.map F x q = 1 := by
  rw [FundamentalGroup.mapOfEq_apply]
  exact loop_cast_eq_one_iff h.symm _
end ThreeManifold.LoopTopology
end

section
open Set Filter Topology
open scoped UpperHalfPlane
namespace ThreeManifold.GluedConstruction
open HyperbolicCore LoopTopology

def clippedPiece (x : Surface×Circle) : Piece :=
  (⟨clipCusp 2 4 (by norm_num) (by norm_num) x.1,
    (clipCusp_height_le 2 4 (by norm_num) (by norm_num) x.1).trans_lt
      (Real.log_lt_log (by norm_num) (by norm_num : (4:ℝ)<8))⟩,x.2)
lemma clippedPiece_continuous : Continuous clippedPiece :=
  (((clipCusp_continuous 2 4 (by norm_num) (by norm_num)).comp continuous_fst).subtype_mk _).prodMk continuous_snd

def blockMap (i : Bool) : C(Surface×Circle,Manifold) :=
  ⟨inclusion i ∘ clippedPiece,(TwoGluing.inclusion_openEmbedding collar gluingMap i).continuous.comp clippedPiece_continuous⟩
lemma clippedPiece_fixed (x : Surface) (hx : height x ≤ Real.log 4) (u : Circle) :
    clippedPiece (x,u) = (⟨x,hx.trans_lt (Real.log_lt_log (by norm_num) (by norm_num : (4:ℝ)<8))⟩,u) := by
  apply Prod.ext
  · apply Subtype.ext; exact clipCusp_eq_self 2 4 (by norm_num) (by norm_num) hx
  · rfl

def boundarySurface (u : Circle) : Surface :=
  ((cuspCoordinates 2 (by norm_num)).symm (⟨4,by norm_num⟩,u)).1
lemma boundarySurface_continuous : Continuous boundarySurface :=
  continuous_subtype_val.comp ((cuspCoordinates 2 (by norm_num)).symm.continuous.comp (continuous_const.prodMk continuous_id))
lemma boundarySurface_height (u : Circle) : height (boundarySurface u) = Real.log 4 := by
  unfold boundarySurface
  rw [height_cuspCoordinates 2 (by norm_num),Homeomorph.apply_symm_apply]
lemma boundarySurface_horoline (t : ℝ) :
    boundarySurface ((6*t : ℝ) : Circle) = projection (horoline 4 t (by norm_num)) := by
  have hh := cuspCoordinates_apply 2 (by norm_num) (horoline 4 t (by norm_num)) (by norm_num [horoline])
  have he : (cuspCoordinates 2 (by norm_num))
      ⟨projection (horoline 4 t (by norm_num)),⟨horoline 4 t (by norm_num),by norm_num [horoline],rfl⟩⟩ =
      (⟨4,by norm_num⟩,((6*t : ℝ) : Circle)) := by simpa [horoline] using hh
  change ((cuspCoordinates 2 (by norm_num)).symm (⟨4,by norm_num⟩,((6*t:ℝ):Circle))).1 = _
  rw [← he,Homeomorph.symm_apply_apply]

def torusPoint (z : Circle×Circle) : collar :=
  collarCoordinates.symm (⟨4,by norm_num,by norm_num⟩,z)
lemma blockMap_torus (i : Bool) (z : Circle×Circle) :
    blockMap i (boundarySurface z.1,z.2) = inclusion i (torusPoint z).1 := by
  change inclusion i (clippedPiece (boundarySurface z.1,z.2)) = _
  rw [clippedPiece_fixed _ (by rw [boundarySurface_height])]
  rfl
lemma gluing_torus (z : Circle×Circle) : gluingMap.symm (torusPoint z) = torusPoint (torusShear z) := by
  change collarCoordinates.symm ((collarFlip.prodCongr torusShear.symm).symm
    (collarCoordinates (collarCoordinates.symm (⟨4,by norm_num,by norm_num⟩,z)))) = _
  rw [Homeomorph.apply_symm_apply]
  apply congrArg collarCoordinates.symm
  apply Prod.ext
  · apply Subtype.ext
    norm_num [collarFlip]
  · rfl
lemma blockMap_torus_shear (z : Circle×Circle) :
    blockMap true (boundarySurface z.1,z.2) =
      blockMap false (boundarySurface (z.1+z.2),z.1) := by
  change blockMap true (boundarySurface z.1,z.2) =
    blockMap false (boundarySurface (torusShear z).1,(torusShear z).2)
  rw [blockMap_torus true z,blockMap_torus false (torusShear z)]
  have h := TwoGluing.inclusion_symm_transition collar gluingMap (torusPoint z)
  rw [gluing_torus] at h
  exact h

abbrev baseSurface : Surface := projection (horoline 4 0 (by norm_num))
abbrev wholeBase : Surface×Circle := (baseSurface,0)
def basePoint : Manifold := blockMap false wholeBase
lemma boundarySurface_zero : boundarySurface 0 = baseSurface := by simpa using boundarySurface_horoline 0
lemma blockMap_base (i : Bool) : blockMap i wholeBase = basePoint := by
  cases i
  · rfl
  · have h := blockMap_torus_shear (0,0)
    change blockMap true (baseSurface,0) = blockMap false (baseSurface,0)
    simpa only [zero_add,boundarySurface_zero] using h

def circlePath : Path (0 : Circle) 0 where
  toFun t := ((6*(t : ℝ) : ℝ) : Circle)
  continuous_toFun := (AddCircle.continuous_mk' 6).comp (continuous_const.mul continuous_subtype_val)
  source' := by simp
  target' := by change ((6*(1:ℝ) : ℝ) : Circle) = 0; simp

def circleClass : FundamentalGroup Circle 0 := Path.Homotopic.Quotient.mk circlePath

def blockHom (i : Bool) : FundamentalGroup (Surface×Circle) wholeBase →* FundamentalGroup Manifold basePoint :=
  FundamentalGroup.mapOfEq (blockMap i) (blockMap_base i)
def surfaceHom (i : Bool) : FundamentalGroup Surface baseSurface →* FundamentalGroup Manifold basePoint :=
  (blockHom i).comp (leftHom (0 : Circle))
def fiberClass (i : Bool) : FundamentalGroup Manifold basePoint :=
  blockHom i (pair 1 circleClass)
def boundaryImage (i : Bool) : FundamentalGroup Manifold basePoint :=
  surfaceHom i (boundaryClass 4 (by norm_num))
lemma fiber_commutes_surface (i : Bool) (a : FundamentalGroup Surface baseSurface) :
    Commute (fiberClass i) (surfaceHom i a) :=
  ((pair_commute a circleClass).symm).map (blockHom i)
lemma boundaryImage_commutator (i : Bool) :
    ∃ a b : FundamentalGroup Manifold basePoint, boundaryImage i = a*b*a⁻¹*b⁻¹ ∧
      Commute (fiberClass i) a ∧ Commute (fiberClass i) b := by
  obtain ⟨a,b,h⟩ := boundaryClass_commutator 4 (by norm_num)
  refine ⟨surfaceHom i a,surfaceHom i b,?_,fiber_commutes_surface i a,fiber_commutes_surface i b⟩
  change surfaceHom i (boundaryClass 4 _) = _
  rw [h]; simp only [map_mul,map_inv]
end ThreeManifold.GluedConstruction
end

open Set Filter Topology
namespace ThreeManifold.GluedConstruction
open HyperbolicCore LoopTopology
lemma blockHom_mk (i : Bool) (p : Path wholeBase wholeBase) :
    blockHom i (Path.Homotopic.Quotient.mk p) = Path.Homotopic.Quotient.mk
      ((p.map (blockMap i).continuous).cast (blockMap_base i).symm (blockMap_base i).symm) := by
  exact FundamentalGroup.mapOfEq_apply _ _ _
lemma shear_fiber : fiberClass true = boundaryImage false := by
  change blockHom true (Path.Homotopic.Quotient.mk ((Path.refl baseSurface).prod circlePath)) =
    blockHom false (Path.Homotopic.Quotient.mk ((boundaryPath 4 (by norm_num)).prod (Path.refl 0)))
  rw [blockHom_mk,blockHom_mk]
  congr 1
  apply Path.ext
  funext t
  change blockMap true (baseSurface,((6*(t:ℝ):ℝ):Circle)) =
    blockMap false (projection (horoline 4 t (by norm_num)),0)
  rw [← boundarySurface_zero,← boundarySurface_horoline]
  simpa only [zero_add] using blockMap_torus_shear (0,((6*(t:ℝ):ℝ):Circle))
lemma shear_boundary : boundaryImage true = boundaryImage false * fiberClass false := by
  change blockHom true (pair (boundaryClass 4 (by norm_num)) 1) =
    blockHom false (pair (boundaryClass 4 (by norm_num)) 1) * blockHom false (pair 1 circleClass)
  rw [← map_mul,← pair_split]
  change blockHom true (Path.Homotopic.Quotient.mk ((boundaryPath 4 (by norm_num)).prod (Path.refl 0))) =
    blockHom false (Path.Homotopic.Quotient.mk ((boundaryPath 4 (by norm_num)).prod circlePath))
  rw [blockHom_mk,blockHom_mk]
  congr 1
  apply Path.ext
  funext t
  change blockMap true (projection (horoline 4 t (by norm_num)),0) =
    blockMap false (projection (horoline 4 t (by norm_num)),((6*(t:ℝ):ℝ):Circle))
  rw [← boundarySurface_horoline]
  simpa only [add_zero] using blockMap_torus_shear (((6*(t:ℝ):ℝ):Circle),0)
lemma fibers_commute : Commute (fiberClass false) (fiberClass true) := by
  rw [shear_fiber]
  exact fiber_commutes_surface false (boundaryClass 4 (by norm_num))

theorem actual_loop_relations :
    ∃ a b c d : FundamentalGroup Manifold basePoint,
      Commute (fiberClass false) (fiberClass true) ∧
      Commute (fiberClass false) a ∧ Commute (fiberClass false) b ∧
      Commute (fiberClass true) c ∧ Commute (fiberClass true) d ∧
      fiberClass true = a*b*a⁻¹*b⁻¹ ∧
      fiberClass true * fiberClass false = c*d*c⁻¹*d⁻¹ := by
  obtain ⟨a,b,h,hfa,hfb⟩ := boundaryImage_commutator false
  obtain ⟨c,d,k,hhc,hhd⟩ := boundaryImage_commutator true
  exact ⟨a,b,c,d,fibers_commute,hfa,hfb,hhc,hhd,
    shear_fiber.trans h,(congrArg (fun z => z*fiberClass false) shear_fiber).trans (shear_boundary.symm.trans k)⟩
end ThreeManifold.GluedConstruction

end

end OAI
