import OAI.Combinatorics.ThinTrees.Truncation

namespace OAI

universe uE uI uJ uV uI2 uI3 uV2 uW uJ2 uV3 uE2 uT uJ3 uH uI4

section

namespace StrongThinTree.Duality
noncomputable section
open Finset
open scoped Classical
variable {E : Type uE} {I : Type uI} [AddCommGroup E] [Module ℝ E] [Fintype I]

def strictUpperImage (S : Set E) (F : I → E → ℝ) : Set (I → ℝ) :=
  {v | ∃x ∈ S, ∀i, F i x < v i}

omit [AddCommGroup E] [Module ℝ E] in
lemma strictUpperImage_isOpen (S : Set E) (F : I → E → ℝ) :
    IsOpen (strictUpperImage S F) := by
  have he : strictUpperImage S F = ⋃x ∈ S, ⋂i, {v : I → ℝ | F i x < v i} := by
    ext v; simp [strictUpperImage]
  rw [he]
  exact isOpen_iUnion (fun x => isOpen_iUnion (fun _ => isOpen_iInter_of_finite
    (fun i => isOpen_lt continuous_const (continuous_apply i))))

omit [Fintype I] in
lemma strictUpperImage_convex (S : Set E) (F : I → E → ℝ)
    (hS : Convex ℝ S) (hF : ∀i, ConvexOn ℝ S (F i)) :
    Convex ℝ (strictUpperImage S F) := by
  intro u hu v hv a b ha hb hab
  obtain ⟨x,hx,hxu⟩ := hu
  obtain ⟨y,hy,hyv⟩ := hv
  refine ⟨a • x+b • y,hS hx hy ha hb hab,?_⟩
  intro i
  have hf := (hF i).2 hx hy ha hb hab
  change F i (a • x+b • y) < a*u i+b*v i
  change F i (a • x+b • y) ≤ a*F i x+b*F i y at hf
  have hlt : a*F i x+b*F i y < a*u i+b*v i := by
    by_cases ha0 : a=0
    · have hb1 : b=1 := by linarith
      simpa [ha0,hb1] using hyv i
    · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left (hxu i) hapos)
        (mul_le_mul_of_nonneg_left (hyv i).le hb)
  exact hf.trans_lt hlt

lemma functional_coordinates (l : (I → ℝ) →L[ℝ] ℝ) (v : I → ℝ) :
    l v = ∑i, l (Pi.single i 1)*v i := by
  have he : v=∑i, v i • Pi.single i (1:ℝ) := by
    funext j
    simp [Pi.single_apply]
  calc
    l v = l (∑i, v i • Pi.single i (1:ℝ)) := congrArg l he
    _ = ∑i, l (Pi.single i 1)*v i := by
      rw [map_sum]
      apply sum_congr rfl
      intro i _
      rw [map_smul]
      simp only [smul_eq_mul,mul_comm]

lemma convex_alternative (S : Set E) (hS : Convex ℝ S) (hne : S.Nonempty)
    (F : I → E → ℝ) (hF : ∀i, ConvexOn ℝ S (F i))
    (hinfeasible : ¬∃x ∈ S, ∀i, F i x < 0) :
    ∃w : I → ℝ, (∀i, 0 ≤ w i) ∧ (∑i, w i)=1 ∧
      ∀x ∈ S, 0 ≤ ∑i, w i*F i x := by
  have hzero : (0:I → ℝ) ∉ strictUpperImage S F := hinfeasible
  obtain ⟨l,hl⟩ := geometric_hahn_banach_point_open (strictUpperImage_convex S F hS hF)
    (strictUpperImage_isOpen S F) hzero
  simp only [map_zero] at hl
  let w : I → ℝ := fun i => l (Pi.single i 1)
  obtain ⟨x₀,hx₀⟩ := hne
  let v₀ : I → ℝ := fun i => F i x₀+1
  have hv₀ : v₀ ∈ strictUpperImage S F := ⟨x₀,hx₀,fun i => by dsimp [v₀]; linarith⟩
  have hlv : 0 < l v₀ := hl v₀ hv₀
  have hw : ∀i, 0 ≤ w i := by
    intro i
    by_contra hh
    have hi : w i < 0 := lt_of_not_ge hh
    let t := (l v₀+1)/(-w i)
    have ht : 0 ≤ t := div_nonneg (by linarith only [hlv]) (neg_pos.mpr hi).le
    have hv : v₀+t • Pi.single i 1 ∈ strictUpperImage S F := by
      refine ⟨x₀,hx₀,?_⟩
      intro j
      change F j x₀ < v₀ j+t*((Pi.single i (1:ℝ) : I → ℝ) j)
      have hj : 0 ≤ ((Pi.single i (1:ℝ) : I → ℝ) j) := by simp [Pi.single_apply]; split_ifs <;> norm_num
      exact (show F j x₀ < v₀ j by dsimp [v₀]; linarith).trans_le (le_add_of_nonneg_right (mul_nonneg ht hj))
    have hh := hl _ hv
    rw [map_add,map_smul] at hh
    change 0 < l v₀+t*w i at hh
    have hid : t*w i=-(l v₀+1) := by dsimp [t]; field_simp [ne_of_lt hi]
    linarith only [hh,hid]
  let W := ∑i, w i
  have hW : 0 < W := by
    have hWnon : 0 ≤ W := sum_nonneg (fun i _ => hw i)
    by_contra hh
    have hW0 : W=0 := le_antisymm (le_of_not_gt hh) hWnon
    have hw0 : ∀i, w i=0 := fun i => (sum_eq_zero_iff_of_nonneg (fun i _ => hw i)).mp hW0 i (mem_univ i)
    rw [functional_coordinates] at hlv
    have hz : ∑i, l (Pi.single i 1)*v₀ i=0 := by
      change (∑i, w i*v₀ i)=0
      simp [hw0]
    linarith only [hlv,hz]
  have hbound : ∀x ∈ S, 0 ≤ ∑i, w i*F i x := by
    intro x hx
    apply le_of_forall_pos_lt_add
    intro ε hε
    have heps : 0 < ε/W := div_pos hε hW
    have hv : (fun i => F i x+ε/W) ∈ strictUpperImage S F :=
      ⟨x,hx,fun i => lt_add_of_pos_right _ heps⟩
    have hh := hl _ hv
    rw [functional_coordinates] at hh
    change 0 < ∑i, w i*(F i x+ε/W) at hh
    simp only [mul_add,sum_add_distrib,←sum_mul] at hh
    have heq : W*(ε/W)=ε := by field_simp
    change 0 < (∑i, w i*F i x)+W*(ε/W) at hh
    rwa [heq] at hh
  refine ⟨fun i => w i/W,fun i => div_nonneg (hw i) hW.le,?_,?_⟩
  · rw [←sum_div]
    exact div_self hW.ne'
  · intro x hx
    simp only [div_mul_eq_mul_div,←sum_div]
    exact div_nonneg (hbound x hx) hW.le
variable {J : Type uJ} [Fintype J]

lemma slater_certificate (S : Set E) (hS : Convex ℝ S)
    (f : I → E → ℝ) (g : J → E → ℝ)
    (hf : ∀i, ConvexOn ℝ S (f i)) (hg : ∀j, ConvexOn ℝ S (g j))
    (hslater : ∃x ∈ S, ∀j, g j x < 0) (K : ℝ)
    (hinfeasible : ¬∃x ∈ S, (∀i, f i x < K) ∧ (∀j, g j x < 0)) :
    ∃lam : I → ℝ, ∃y : J → ℝ, (∀i, 0 ≤ lam i) ∧ (∑i, lam i)=1 ∧
      (∀j, 0 ≤ y j) ∧ ∀x ∈ S, K ≤ (∑i, lam i*f i x)+(∑j, y j*g j x) := by
  let F : I ⊕ J → E → ℝ := Sum.elim (fun i x => f i x-K) g
  have hF : ∀i, ConvexOn ℝ S (F i) := by
    intro i
    cases i with
    | inl i =>
      refine ⟨hS,?_⟩
      intro x hx y hy a b ha hb hab
      have hh := (hf i).2 hx hy ha hb hab
      change f i (a • x+b • y)-K ≤ a*(f i x-K)+b*(f i y-K)
      change f i (a • x+b • y) ≤ a*f i x+b*f i y at hh
      nlinarith only [hh,congrArg (fun z : ℝ => z*K) hab]
    | inr j => exact hg j
  have hnone : ¬∃x ∈ S, ∀i, F i x < 0 := by
    intro ⟨x,hx,h⟩
    apply hinfeasible
    exact ⟨x,hx,fun i => sub_neg.mp (h (Sum.inl i)),fun j => h (Sum.inr j)⟩
  obtain ⟨x₀,hx₀,hg₀⟩ := hslater
  obtain ⟨w,hw,hws,hwb⟩ := convex_alternative S hS ⟨x₀,hx₀⟩ F hF hnone
  let p := ∑i, w (Sum.inl i)
  have hpnon : 0 ≤ p := sum_nonneg (fun i _ => hw (Sum.inl i))
  have hsum : p+(∑j, w (Sum.inr j))=1 := by simpa only [p,Fintype.sum_sum_type] using hws
  have hp : 0 < p := by
    by_contra hh
    have hp0 : p=0 := le_antisymm (le_of_not_gt hh) hpnon
    have hwi0 : ∀i, w (Sum.inl i)=0 := fun i =>
      (sum_eq_zero_iff_of_nonneg (fun i _ => hw (Sum.inl i))).mp hp0 i (mem_univ i)
    have hjpos : 0 < ∑j, w (Sum.inr j) := by linarith only [hsum,hp0]
    obtain ⟨j,hj,hjpos⟩ := (sum_pos_iff_of_nonneg (fun j _ => hw (Sum.inr j))).mp hjpos
    have hgneg : (∑j, w (Sum.inr j)*g j x₀) < 0 := by
      apply sum_neg' (fun j _ => mul_nonpos_of_nonneg_of_nonpos (hw (Sum.inr j)) (hg₀ j).le)
      exact ⟨j,mem_univ j,mul_neg_of_pos_of_neg hjpos (hg₀ j)⟩
    have hh := hwb x₀ hx₀
    simp only [Fintype.sum_sum_type,F,Sum.elim_inl,Sum.elim_inr,hwi0,zero_mul,sum_const_zero,zero_add] at hh
    linarith only [hh,hgneg]
  refine ⟨fun i => w (Sum.inl i)/p,fun j => w (Sum.inr j)/p,
    fun i => div_nonneg (hw (Sum.inl i)) hp.le,?_,
    fun j => div_nonneg (hw (Sum.inr j)) hp.le,?_⟩
  · rw [←sum_div]
    exact div_self hp.ne'
  · intro x hx
    have hh := hwb x hx
    simp only [Fintype.sum_sum_type,F,Sum.elim_inl,Sum.elim_inr,mul_sub,sum_sub_distrib,←sum_mul] at hh
    simp only [div_mul_eq_mul_div,←sum_div,←add_div]
    apply (le_div_iff₀ hp).mpr
    change 0 ≤ (∑i, w (Sum.inl i)*f i x)-p*K+(∑j, w (Sum.inr j)*g j x) at hh
    linarith only [hh]

lemma strict_feasible_of_dual_bound (S : Set E) (hS : Convex ℝ S)
    (f : I → E → ℝ) (g : J → E → ℝ)
    (hf : ∀i, ConvexOn ℝ S (f i)) (hg : ∀j, ConvexOn ℝ S (g j))
    (hslater : ∃x ∈ S, ∀j, g j x < 0) (K : ℝ)
    (hdual : ∀lam : I → ℝ, ∀y : J → ℝ, (∀i, 0 ≤ lam i) → (∑i, lam i)=1 →
      (∀j, 0 ≤ y j) → ∃x ∈ S, (∑i, lam i*f i x)+(∑j, y j*g j x) < K) :
    ∃x ∈ S, (∀i, f i x < K) ∧ (∀j, g j x < 0) := by
  by_contra hh
  obtain ⟨lam,y,hlam,hlams,hy,hbound⟩ := slater_certificate S hS f g hf hg hslater K hh
  obtain ⟨x,hx,hval⟩ := hdual lam y hlam hlams hy
  exact (not_lt_of_ge (hbound x hx)) hval
end
end StrongThinTree.Duality

namespace StrongThinTree.MatrixDual
noncomputable section
open Matrix Finset
open scoped Classical MatrixOrder
variable {V : Type uV} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
lemma quadratic_symm {D : Matrix V V ℝ} (hD : D.IsHermitian) (x y : V → ℝ) :
    x ⬝ᵥ (D *ᵥ y) = y ⬝ᵥ (D *ᵥ x) := by
  have hsym : D.transpose=D := isHermitian_iff_isSymm.mp hD
  rw [dotProduct_mulVec,dotProduct_comm,←vecMul_transpose,hsym]

lemma solve {D : Matrix V V ℝ} (hD : D.PosDef) (b : V → ℝ) :
    D *ᵥ (D⁻¹ *ᵥ b)=b := by
  rw [mulVec_mulVec,mul_nonsing_inv D ((isUnit_iff_isUnit_det D).mp hD.isUnit),one_mulVec]

lemma inverse_quadratic_variational {D : Matrix V V ℝ} (hD : D.PosDef) (b x : V → ℝ) :
    2*(b ⬝ᵥ x)-x ⬝ᵥ (D *ᵥ x) ≤ b ⬝ᵥ (D⁻¹ *ᵥ b) := by
  let y := D⁻¹ *ᵥ b
  have hDy : D *ᵥ y=b := solve hD b
  have hs : y ⬝ᵥ (D *ᵥ x)=x ⬝ᵥ b := by rw [quadratic_symm hD.isHermitian,hDy]
  have hh := hD.posSemidef.dotProduct_mulVec_nonneg (x-y)
  simp only [star_trivial,mulVec_sub,sub_dotProduct,dotProduct_sub,hDy,hs,
    dotProduct_comm x b,dotProduct_comm y b] at hh
  change 2*(b ⬝ᵥ x)-x ⬝ᵥ (D *ᵥ x) ≤ b ⬝ᵥ y
  linarith only [hh]

lemma inverse_quadratic_attained {D : Matrix V V ℝ} (hD : D.PosDef) (b : V → ℝ) :
    b ⬝ᵥ (D⁻¹ *ᵥ b)=2*(b ⬝ᵥ (D⁻¹ *ᵥ b))-(D⁻¹ *ᵥ b) ⬝ᵥ (D *ᵥ (D⁻¹ *ᵥ b)) := by
  rw [solve hD b,dotProduct_comm (D⁻¹ *ᵥ b) b]
  ring

omit [Fintype V] [DecidableEq V] in
lemma posDef_convex : Convex ℝ {D : Matrix V V ℝ | D.PosDef} := by
  intro X hX Y hY a b ha hb hab
  by_cases ha0 : a=0
  · have hb1 : b=1 := by linarith only [hab,ha0]
    simpa [ha0,hb1] using hY
  · exact (hX.smul (lt_of_le_of_ne ha (Ne.symm ha0))).add_posSemidef (hY.posSemidef.smul hb)

lemma inverse_quadratic_convex (v : V → ℝ) :
    ConvexOn ℝ {D : Matrix V V ℝ | D.PosDef} (fun D => v ⬝ᵥ (D⁻¹ *ᵥ v)) := by
  refine ⟨posDef_convex,?_⟩
  intro X hX Y hY a b ha hb hab
  let D := a • X+b • Y
  have hD : D.PosDef := posDef_convex hX hY ha hb hab
  let z := D⁻¹ *ᵥ v
  have hXv := inverse_quadratic_variational hX v z
  have hYv := inverse_quadratic_variational hY v z
  have hDv := inverse_quadratic_attained hD v
  have hf : 2*(v ⬝ᵥ z)-z ⬝ᵥ (D *ᵥ z) =
      a*(2*(v ⬝ᵥ z)-z ⬝ᵥ (X *ᵥ z))+b*(2*(v ⬝ᵥ z)-z ⬝ᵥ (Y *ᵥ z)) := by
    dsimp [D]
    simp only [add_mulVec,smul_mulVec,dotProduct_add,dotProduct_smul,smul_eq_mul]
    nlinarith only [congrArg (fun t : ℝ => t*(v ⬝ᵥ z)) hab]
  change v ⬝ᵥ (D⁻¹ *ᵥ v) ≤ a*(v ⬝ᵥ (X⁻¹ *ᵥ v))+b*(v ⬝ᵥ (Y⁻¹ *ᵥ v))
  rw [hDv]
  change 2*(v ⬝ᵥ z)-z ⬝ᵥ (D *ᵥ z) ≤ _
  rw [hf]
  exact add_le_add (mul_le_mul_of_nonneg_left hXv ha) (mul_le_mul_of_nonneg_left hYv hb)

omit [DecidableEq V] in
lemma cut_quadratic_convex (v : V → ℝ) (c : ℝ) :
    ConvexOn ℝ {D : Matrix V V ℝ | D.PosDef} (fun D => v ⬝ᵥ (D *ᵥ v)-c) := by
  refine ⟨posDef_convex,?_⟩
  intro X hX Y hY a b ha hb hab
  simp only [add_mulVec,smul_mulVec,dotProduct_add,dotProduct_smul,smul_eq_mul]
  nlinarith only [congrArg (fun t : ℝ => t*c) hab]

lemma posDef_sqrt {A : Matrix V V ℝ} (hA : A.PosDef) : (CFC.sqrt A).PosDef := by
  apply (CFC.sqrt_nonneg A).posSemidef.posDef_iff_isUnit.mpr
  apply (isUnit_pow_iff (by decide : 2 ≠ 0)).mp
  rw [CFC.sq_sqrt A hA.posSemidef.nonneg]
  exact hA.isUnit

lemma congr_posDef {A S : Matrix V V ℝ} (hA : A.PosDef)
    (hSH : S.IsHermitian) (hSU : IsUnit S) : (S*A*S).PosDef := by
  simpa only [hSH.eq] using hA.conjTranspose_mul_mul_same
    (mulVec_injective_iff_isUnit.mpr hSU)

lemma trace_objective_attained {A Z : Matrix V V ℝ} (hA : A.PosDef) (hZ : Z.PosDef) :
    ∃ D : Matrix V V ℝ, D.PosDef ∧
      (A*D⁻¹).trace+(Z*D).trace =
        2*(CFC.sqrt (CFC.sqrt Z*A*CFC.sqrt Z)).trace := by
  let S := CFC.sqrt Z
  have hS : S.PosDef := posDef_sqrt hZ
  have hSS : S*S=Z := CFC.sqrt_mul_sqrt_self Z hZ.posSemidef.nonneg
  have hSi : S*S⁻¹=1 := mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hS.isUnit)
  have hiS : S⁻¹*S=1 := nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp hS.isUnit)
  let C := S*A*S
  have hC : C.PosDef := congr_posDef hA hS.isHermitian hS.isUnit
  let T := CFC.sqrt C
  have hT : T.PosDef := posDef_sqrt hC
  have hTT : T*T=C := CFC.sqrt_mul_sqrt_self C hC.posSemidef.nonneg
  have hTi : T*T⁻¹=1 := mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hT.isUnit)
  let D := S⁻¹*T*S⁻¹
  have hD : D.PosDef := congr_posDef hT hS.inv.isHermitian hS.inv.isUnit
  have hDinv : D⁻¹=S*T⁻¹*S := by
    apply inv_eq_right_inv
    dsimp [D]
    simp only [mul_assoc,←mul_assoc S⁻¹ S,hiS,←mul_assoc T T⁻¹,hTi,one_mul]
  have hAeq : A=S⁻¹*(T*T)*S⁻¹ := by
    rw [hTT]
    dsimp [C]
    simp only [mul_assoc,hSi,mul_one,←mul_assoc S⁻¹ S,hiS,one_mul]
  have htA : (A*D⁻¹).trace=T.trace := by
    rw [hDinv,hAeq]
    have heq : S⁻¹*(T*T)*S⁻¹*(S*T⁻¹*S)=S⁻¹*T*S := by
      simp only [mul_assoc,←mul_assoc S⁻¹ S,hiS,one_mul]
      simp only [←mul_assoc T T⁻¹,hTi,one_mul]
    rw [heq,Matrix.trace_mul_cycle,hSi,one_mul]
  have htZ : (Z*D).trace=T.trace := by
    rw [←hSS]
    dsimp [D]
    have heq : S*S*(S⁻¹*T*S⁻¹)=S*T*S⁻¹ := by
      simp only [mul_assoc,←mul_assoc S S⁻¹,hSi,one_mul]
    rw [heq,Matrix.trace_mul_cycle,hiS,one_mul]
  refine ⟨D,hD,?_⟩
  change (A*D⁻¹).trace+(Z*D).trace=2*T.trace
  rw [htA,htZ]
  ring

open Filter Topology
open scoped Matrix.Norms.L2Operator

lemma sqrt_tendsto {I : Type uI2} {l : Filter I} {A : Matrix V V ℝ}
    (hA : A.PosSemidef) {f : I → Matrix V V ℝ}
    (hf : Tendsto f l (𝓝 A)) (hfp : ∀ᶠ i in l, (f i).PosSemidef) :
    Tendsto (fun i => CFC.sqrt (f i)) l (𝓝 (CFC.sqrt A)) := by
  apply (CFC.continuousOn_sqrt A hA.nonneg).tendsto.comp
  exact tendsto_nhdsWithin_iff.mpr ⟨hf,hfp.mono (fun i hi => hi.nonneg)⟩

lemma traceRoot_tendsto {I : Type uI3} {l : Filter I} {A Z : Matrix V V ℝ}
    (hA : A.PosSemidef) (hZ : Z.PosSemidef) {f g : I → Matrix V V ℝ}
    (hf : Tendsto f l (𝓝 A)) (hg : Tendsto g l (𝓝 Z))
    (hfp : ∀ᶠ i in l, (f i).PosSemidef) (hgp : ∀ᶠ i in l, (g i).PosSemidef) :
    Tendsto (fun i => 2*(CFC.sqrt (CFC.sqrt (g i)*f i*CFC.sqrt (g i))).trace) l
      (𝓝 (2*(CFC.sqrt (CFC.sqrt Z*A*CFC.sqrt Z)).trace)) := by
  have hs := sqrt_tendsto hZ hg hgp
  have hp : (CFC.sqrt Z*A*CFC.sqrt Z).PosSemidef := by
    simpa only [(CFC.sqrt_nonneg Z).posSemidef.isHermitian.eq] using
      hA.conjTranspose_mul_mul_same (CFC.sqrt Z)
  have hps : ∀ᶠ i in l, (CFC.sqrt (g i)*f i*CFC.sqrt (g i)).PosSemidef := by
    filter_upwards [hfp] with i hi
    simpa only [(CFC.sqrt_nonneg (g i)).posSemidef.isHermitian.eq] using
      hi.conjTranspose_mul_mul_same (CFC.sqrt (g i))
  have ht := sqrt_tendsto hp ((hs.mul hf).mul hs) hps
  have htr := (continuous_id.matrix_trace.tendsto _).comp ht
  exact htr.const_mul 2

lemma trace_objective_approx {A Z : Matrix V V ℝ} (hA : A.PosSemidef) (hZ : Z.PosSemidef)
    {K : ℝ} (hK : 2*(CFC.sqrt (CFC.sqrt Z*A*CFC.sqrt Z)).trace < K) :
    ∃ D : Matrix V V ℝ, D.PosDef ∧ (A*D⁻¹).trace+(Z*D).trace < K := by
  let f : ℝ → Matrix V V ℝ := fun t => A+t•1
  let g : ℝ → Matrix V V ℝ := fun t => Z+t•1
  have hf : Tendsto f (𝓝[>] 0) (𝓝 A) := by
    have hc : Continuous f := by dsimp [f]; fun_prop
    simpa [f] using (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  have hg : Tendsto g (𝓝[>] 0) (𝓝 Z) := by
    have hc : Continuous g := by dsimp [g]; fun_prop
    simpa [g] using (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0<t := self_mem_nhdsWithin
  have hfp : ∀t, 0<t → (f t).PosDef := by
    intro t ht
    simpa [f,add_comm] using (Matrix.PosDef.one.smul ht).add_posSemidef hA
  have hgp : ∀t, 0<t → (g t).PosDef := by
    intro t ht
    simpa [g,add_comm] using (Matrix.PosDef.one.smul ht).add_posSemidef hZ
  have hv := traceRoot_tendsto hA hZ hf hg
    (hpos.mono (fun t ht => (hfp t ht).posSemidef))
    (hpos.mono (fun t ht => (hgp t ht).posSemidef))
  obtain ⟨t,ht,htK⟩ := (hpos.and (hv.eventually_lt_const hK)).exists
  obtain ⟨D,hD,heq⟩ := trace_objective_attained (hfp t ht) (hgp t ht)
  have hterms : (A*D⁻¹).trace+(Z*D).trace ≤ ((f t)*D⁻¹).trace+((g t)*D).trace := by
    dsimp [f,g]
    simp only [add_mul,smul_mul_assoc,one_mul,trace_add,trace_smul,smul_eq_mul]
    nlinarith only [mul_nonneg ht.le hD.inv.posSemidef.trace_nonneg,
      mul_nonneg ht.le hD.posSemidef.trace_nonneg]
  exact ⟨D,hD,hterms.trans_lt (heq.trans_lt htK)⟩
end
end StrongThinTree.MatrixDual

namespace StrongThinTree.Polar
noncomputable section
open Matrix Finset
open scoped Classical MatrixOrder Matrix.Norms.L2Operator
variable {V : Type uV2} {W : Type uW} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

lemma sqrt_eq_real_cfc {A : Matrix V V ℝ} (hA : A.PosSemidef) :
    CFC.sqrt A=cfc Real.sqrt A := by
  rw [CFC.sqrt_eq_cfc,cfc_nnreal_eq_real _ _ hA.nonneg]
  unfold Real.sqrt
  rfl

lemma trace_sqrt_roots {A : Matrix V V ℝ} (hA : A.PosSemidef) :
    (CFC.sqrt A).trace=(A.charpoly.roots.map Real.sqrt).sum := by
  rw [sqrt_eq_real_cfc hA,hA.isHermitian.cfc_eq]
  unfold Matrix.IsHermitian.cfc
  rw [Unitary.conjStarAlgAut_apply,Matrix.trace_mul_cycle]
  simp only [Unitary.coe_star_mul_self,one_mul,trace_diagonal]
  rw [hA.isHermitian.roots_charpoly_eq_eigenvalues,Multiset.map_map]
  rfl

lemma trace_sqrt_mul_comm (A : Matrix V W ℝ) (B : Matrix W V ℝ)
    (hAB : (A*B).PosSemidef) (hBA : (B*A).PosSemidef) :
    (CFC.sqrt (A*B)).trace=(CFC.sqrt (B*A)).trace := by
  rw [trace_sqrt_roots hAB,trace_sqrt_roots hBA]
  have heq := congrArg (fun p : Polynomial ℝ => (p.roots.map Real.sqrt).sum)
    (Matrix.charpoly_mul_comm' A B)
  rw [Polynomial.roots_mul (mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) (A*B).charpoly_monic.ne_zero),
    Polynomial.roots_mul (mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) (B*A).charpoly_monic.ne_zero)] at heq
  have hz (n : ℕ) : ((n • ({0} : Multiset ℝ)).map Real.sqrt).sum=0 := by
    induction n with
    | zero => simp
    | succ n hn => simp [succ_nsmul,Multiset.map_add,hn]
  simpa [Polynomial.roots_X_pow,Multiset.map_add,hz] using heq

lemma trace_sqrt_gram (M : Matrix V W ℝ) :
    (CFC.sqrt (M*Mᵀ)).trace=(CFC.sqrt (Mᵀ*M)).trace := by
  exact trace_sqrt_mul_comm M Mᵀ
    (by simpa using posSemidef_self_mul_conjTranspose M)
    (by simpa using posSemidef_conjTranspose_mul_self M)

lemma cfc_continuousOn {A : Matrix V V ℝ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    ContinuousOn f (spectrum ℝ A) := by
  rw [hA.spectrum_real_eq_range_eigenvalues]
  exact (Set.finite_range _).continuousOn f

lemma inverse_sqrt_scalar {x : ℝ} (hx : 0 ≤ x) : (Real.sqrt x)⁻¹*x=Real.sqrt x := by
  by_cases hx0 : x=0
  · simp [hx0]
  · have hs : Real.sqrt x ≠ 0 := Real.sqrt_ne_zero'.mpr (lt_of_le_of_ne hx (Ne.symm hx0))
    calc
      (Real.sqrt x)⁻¹*x=(Real.sqrt x)⁻¹*(Real.sqrt x*Real.sqrt x) :=
        congrArg (fun t : ℝ => (Real.sqrt x)⁻¹*t) (Real.mul_self_sqrt hx).symm
      _=Real.sqrt x := by rw [←mul_assoc,inv_mul_cancel₀ hs,one_mul]

lemma inverse_sqrt_scalar_bound {x : ℝ} (hx : 0 ≤ x) :
    (Real.sqrt x)⁻¹*x*(Real.sqrt x)⁻¹ ≤ 1 := by
  rw [inverse_sqrt_scalar hx]
  by_cases hs : Real.sqrt x=0
  · simp [hs]
  · simp [hs]

omit [DecidableEq W] in

lemma polar_optimizer (M : Matrix V W ℝ) :
    ∃ U : Matrix W V ℝ, Uᵀ*U ≤ 1 ∧
      (U*M).trace=(CFC.sqrt (M*Mᵀ)).trace := by
  let H := M*Mᵀ
  have hH : H.PosSemidef := by simpa [H] using posSemidef_self_mul_conjTranspose M
  let f : ℝ → ℝ := fun x => (Real.sqrt x)⁻¹
  let P := cfc f H
  have hid : cfc (fun x : ℝ => x) H=H := cfc_id ℝ H hH.isHermitian
  have hP : P.IsHermitian := cfc_predicate f H
  have hPtrans : Pᵀ=P := isHermitian_iff_isSymm.mp hP
  have hPH : P*H=CFC.sqrt H := by
    rw [sqrt_eq_real_cfc hH]
    calc
      P*H=cfc (fun x => f x*x) H := by
        rw [cfc_mul f (fun x => x) H (cfc_continuousOn hH.isHermitian f)
          (cfc_continuousOn hH.isHermitian (fun x => x)),hid]
      _=cfc Real.sqrt H := cfc_congr (fun x hx => inverse_sqrt_scalar (spectrum_nonneg_of_nonneg hH.nonneg hx))
  have hPHP : P*H*P ≤ 1 := by
    have heq : P*H*P=cfc (fun x => f x*x*f x) H := by
      rw [cfc_mul (fun x => f x*x) f H (cfc_continuousOn hH.isHermitian _)
        (cfc_continuousOn hH.isHermitian _),cfc_mul f (fun x => x) H
        (cfc_continuousOn hH.isHermitian _) (cfc_continuousOn hH.isHermitian _),
        hid]
    rw [heq]
    exact cfc_le_one _ _ (fun x hx => inverse_sqrt_scalar_bound (spectrum_nonneg_of_nonneg hH.nonneg hx))
  refine ⟨Mᵀ*P,?_,?_⟩
  · simpa only [transpose_mul,transpose_transpose,hPtrans,Matrix.mul_assoc,H] using hPHP
  · rw [Matrix.trace_mul_cycle]
    change (M*Mᵀ*P).trace=(CFC.sqrt H).trace
    change (H*P).trace=(CFC.sqrt H).trace
    rw [Matrix.trace_mul_comm,hPH]

omit [DecidableEq W] in
lemma norm_sq_mulVec_le {U : Matrix W V ℝ} (hU : Uᵀ*U ≤ 1) (x : V → ℝ) :
    (U *ᵥ x) ⬝ᵥ (U *ᵥ x) ≤ x ⬝ᵥ x := by
  have hp := (Matrix.le_iff.mp hU).dotProduct_mulVec_nonneg x
  simp only [star_trivial,sub_mulVec,one_mulVec,dotProduct_sub] at hp
  have heq : x ⬝ᵥ ((Uᵀ*U) *ᵥ x)=(U *ᵥ x) ⬝ᵥ (U *ᵥ x) := by
    rw [←mulVec_mulVec,dotProduct_mulVec,vecMul_transpose]
  rw [heq] at hp
  linarith only [hp]

variable {J : Type uJ2} [Fintype J] [DecidableEq J]

lemma dual_trace_rectangular (C : Matrix V W ℝ) (Y : Matrix J V ℝ) :
    (CFC.sqrt (CFC.sqrt (Yᵀ*Y)*(C*Cᵀ)*CFC.sqrt (Yᵀ*Y))).trace =
      (CFC.sqrt ((Y*C)*(Y*C)ᵀ)).trace := by
  let S := CFC.sqrt (Yᵀ*Y)
  have hZ : (Yᵀ*Y).PosSemidef := by simpa using posSemidef_conjTranspose_mul_self Y
  have hSH : Sᵀ=S := isHermitian_iff_isSymm.mp (CFC.sqrt_nonneg (Yᵀ*Y)).posSemidef.isHermitian
  have hSS : S*S=Yᵀ*Y := CFC.sqrt_mul_sqrt_self _ hZ.nonneg
  have hleft : S*(C*Cᵀ)*S=(S*C)*(S*C)ᵀ := by
    simp only [transpose_mul,hSH,Matrix.mul_assoc]
  change (CFC.sqrt (S*(C*Cᵀ)*S)).trace=_
  rw [hleft,trace_sqrt_gram,trace_sqrt_gram (Y*C)]
  congr 2
  simp only [transpose_mul,hSH]
  calc
    (Cᵀ*S)*(S*C)=Cᵀ*(S*S)*C := by simp only [Matrix.mul_assoc]
    _=(Cᵀ*Yᵀ)*(Y*C) := by rw [hSS]; simp only [Matrix.mul_assoc]

lemma signed_diag_orthogonal (a : W → ℝ) :
    let D : Matrix W W ℝ := diagonal (fun e => if 0 ≤ a e then (1:ℝ) else -1)
    Dᵀ*D=1 := by
  dsimp
  rw [diagonal_transpose,diagonal_mul_diagonal]
  ext i j
  by_cases hij : i=j
  · subst j
    simp only [diagonal_apply_eq,one_apply_eq]
    split_ifs <;> norm_num
  · simp [diagonal_apply_ne _ hij,one_apply_ne hij]

lemma positive_optimizer (M : Matrix V W ℝ) (w : W → ℝ) (hw : ∀e, 0 ≤ w e) :
    ∃ U : Matrix W V ℝ, Uᵀ*U ≤ 1 ∧ (∀e, 0 ≤ (U*M) e e) ∧
      (CFC.sqrt ((M*diagonal w)*(M*diagonal w)ᵀ)).trace ≤
        ∑e, w e*(U*M) e e := by
  obtain ⟨U,hU,htr⟩ := polar_optimizer (M*diagonal w)
  let a : W → ℝ := fun e => (U*M) e e
  let s : W → ℝ := fun e => if 0 ≤ a e then 1 else -1
  let D : Matrix W W ℝ := diagonal s
  have hDD : Dᵀ*D=1 := signed_diag_orthogonal a
  have hsa (e : W) : s e*a e=|a e| := by
    dsimp [s]
    split_ifs with he
    · simp [abs_of_nonneg he]
    · simp [abs_of_neg (lt_of_not_ge he)]
  have hdiag (e : W) : ((D*U)*M) e e=|a e| := by
    rw [Matrix.mul_assoc]
    change (diagonal s*(U*M)) e e=|a e|
    rw [diagonal_mul]
    exact hsa e
  refine ⟨D*U,?_,fun e => (hdiag e).symm ▸ abs_nonneg _,?_⟩
  · have heq : (D*U)ᵀ*(D*U)=Uᵀ*U := by
      rw [transpose_mul]
      calc
        (Uᵀ*Dᵀ)*(D*U)=Uᵀ*(Dᵀ*D)*U := by simp only [Matrix.mul_assoc]
        _=Uᵀ*U := by rw [hDD,Matrix.mul_one]
    rw [heq]
    exact hU
  · rw [←htr,←Matrix.mul_assoc]
    unfold Matrix.trace
    apply sum_le_sum
    intro e _
    change (U*M*diagonal w) e e ≤ w e*((D*U)*M) e e
    rw [mul_diagonal,hdiag]
    change a e*w e ≤ w e*|a e|
    rw [mul_comm (a e)]
    exact mul_le_mul_of_nonneg_left (le_abs_self _) (hw e)
end
end StrongThinTree.Polar

namespace StrongThinTree.ShortcutDual
noncomputable section
open Matrix Finset Filter Topology
open scoped Classical MatrixOrder Matrix.Norms.L2Operator
variable {V : Type uV3} {E : Type uE2} {T : Type uT} {J : Type uJ3} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E] [Fintype T] [Fintype J]

def boundaryMatrix (b : E → V → ℝ) (O : T → Finset E) (t : T) : Matrix V V ℝ :=
  ((O t).card : ℝ)⁻¹ • ∑e ∈ O t, vecMulVec (b e) (b e)

def boundaryAverage (b : E → V → ℝ) (O : T → Finset E) (t : T)
    (D : Matrix V V ℝ) : ℝ :=
  ((O t).card : ℝ)⁻¹ * ∑e ∈ O t, b e ⬝ᵥ (D⁻¹ *ᵥ b e)

def objectiveMatrix (b : E → V → ℝ) (O : T → Finset E) (lam : T → ℝ) : Matrix V V ℝ :=
  ∑t, lam t • boundaryMatrix b O t

def cutMatrix (c : J → V → ℝ) (y : J → ℝ) : Matrix V V ℝ :=
  ∑j, y j • vecMulVec (c j) (c j)

omit [DecidableEq V] in
lemma outer_posSemidef (v : V → ℝ) : (vecMulVec v v).PosSemidef := by
  simpa using posSemidef_vecMulVec_self_star v

omit [Fintype E] [DecidableEq E] [Fintype T] in
omit [DecidableEq V] in
lemma boundaryMatrix_posSemidef (b : E → V → ℝ) (O : T → Finset E) (t : T) :
    (boundaryMatrix b O t).PosSemidef := by
  apply Matrix.PosSemidef.smul _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  exact Matrix.posSemidef_sum _ (fun e _ => outer_posSemidef (b e))

omit [Fintype E] [DecidableEq E] in
omit [DecidableEq V] in
lemma objectiveMatrix_posSemidef (b : E → V → ℝ) (O : T → Finset E)
    {lam : T → ℝ} (hlam : ∀t, 0 ≤ lam t) : (objectiveMatrix b O lam).PosSemidef := by
  exact Matrix.posSemidef_sum _ (fun t _ => (boundaryMatrix_posSemidef b O t).smul (hlam t))

omit [DecidableEq V] in
lemma cutMatrix_posSemidef (c : J → V → ℝ) {y : J → ℝ} (hy : ∀j, 0 ≤ y j) :
    (cutMatrix c y).PosSemidef := by
  exact Matrix.posSemidef_sum _ (fun j _ => (outer_posSemidef (c j)).smul (hy j))

omit [DecidableEq V] in
lemma trace_outer_mul (v : V → ℝ) (D : Matrix V V ℝ) :
    (vecMulVec v v * D).trace = v ⬝ᵥ (D *ᵥ v) := by
  rw [vecMulVec_mul,trace_vecMulVec,dotProduct_comm,dotProduct_mulVec]

omit [Fintype E] [DecidableEq E] [Fintype T] in
lemma boundaryAverage_convex (b : E → V → ℝ) (O : T → Finset E) (t : T) :
    ConvexOn ℝ {D : Matrix V V ℝ | D.PosDef} (boundaryAverage b O t) := by
  refine ⟨MatrixDual.posDef_convex,?_⟩
  intro X hX Y hY a a' ha ha' haa'
  have hs := sum_le_sum (fun e (_ : e ∈ O t) =>
    (MatrixDual.inverse_quadratic_convex (b e)).2 hX hY ha ha' haa')
  dsimp [boundaryAverage]
  simp only [smul_eq_mul] at hs ⊢
  have h := mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr (Nat.cast_nonneg (O t).card) :
    0 ≤ ((O t).card : ℝ)⁻¹)
  simpa only [sum_add_distrib,←mul_sum,mul_add,mul_left_comm] using h

omit [Fintype E] [DecidableEq E] in
lemma trace_objectiveMatrix (b : E → V → ℝ) (O : T → Finset E)
    (lam : T → ℝ) (D : Matrix V V ℝ) :
    (objectiveMatrix b O lam * D⁻¹).trace = ∑t, lam t * boundaryAverage b O t D := by
  simp only [objectiveMatrix,Finset.sum_mul,smul_mul_assoc,trace_sum,trace_smul,
    boundaryMatrix,boundaryAverage,smul_eq_mul,trace_outer_mul]

lemma trace_cutMatrix (c : J → V → ℝ) (y d : J → ℝ) (D : Matrix V V ℝ) :
    (cutMatrix c y * D).trace - ∑j, y j*d j = ∑j, y j*(c j ⬝ᵥ (D *ᵥ c j)-d j) := by
  simp only [cutMatrix,Finset.sum_mul,smul_mul_assoc,trace_sum,trace_smul,
    smul_eq_mul,trace_outer_mul,mul_sub,sum_sub_distrib]

lemma cut_slater (c : J → V → ℝ) {d : J → ℝ} (hd : ∀j, 0 < d j) :
    ∃D : Matrix V V ℝ, D.PosDef ∧ ∀j, c j ⬝ᵥ (D *ᵥ c j)-d j < 0 := by
  have hlim (j : J) : Tendsto (fun t : ℝ => t*(c j ⬝ᵥ c j)) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ => t*(c j ⬝ᵥ c j)) := by fun_prop
    simpa only [zero_mul] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ t : ℝ in 𝓝[>] 0, ∀j, t*(c j ⬝ᵥ c j) < d j :=
    eventually_all.mpr (fun j => (hlim j).eventually_lt_const (hd j))
  have hup : ∀ᶠ t : ℝ in 𝓝[>] (0:ℝ), t ∈ Set.Ioi 0 := eventually_mem_nhdsWithin
  obtain ⟨t,htd,ht⟩ := (hev.and hup).exists
  refine ⟨t • (1 : Matrix V V ℝ), Matrix.PosDef.one.smul ht, ?_⟩
  intro j
  simpa only [smul_mulVec,one_mulVec,dotProduct_smul,smul_eq_mul,sub_lt_zero] using htd j

omit [Fintype E] [DecidableEq E] in

lemma shortcut_of_trace_bound (b : E → V → ℝ) (O : T → Finset E)
    (c : J → V → ℝ) (d : J → ℝ) (hd : ∀j, 0 < d j) {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀lam : T → ℝ, ∀y : J → ℝ, (∀t, 0 ≤ lam t) → (∑t, lam t)=1 →
      (∀j, 0 ≤ y j) →
      (CFC.sqrt (CFC.sqrt (cutMatrix c y) * objectiveMatrix b O lam *
        CFC.sqrt (cutMatrix c y))).trace^2 ≤ K * ∑j, y j*d j)
    {eta : ℝ} (heta : 0 < eta) :
    ∃D : Matrix V V ℝ, D.PosDef ∧
      (∀t, boundaryAverage b O t D < K+eta) ∧ (∀j, c j ⬝ᵥ (D *ᵥ c j) < d j) := by
  have hs := Duality.strict_feasible_of_dual_bound {D : Matrix V V ℝ | D.PosDef}
    MatrixDual.posDef_convex (boundaryAverage b O) (fun j D => c j ⬝ᵥ (D *ᵥ c j)-d j)
    (boundaryAverage_convex b O) (fun j => MatrixDual.cut_quadratic_convex (c j) (d j))
    (cut_slater c hd) (K+eta)
  obtain ⟨D,hD,hf,hg⟩ := hs (by
    intro lam y hlam hlams hy
    let A := objectiveMatrix b O lam
    let Z := cutMatrix c y
    let N := (CFC.sqrt (CFC.sqrt Z*A*CFC.sqrt Z)).trace
    let v := ∑j, y j*d j
    have hv : 0 ≤ v := sum_nonneg (fun j _ => mul_nonneg (hy j) (hd j).le)
    have hN : 0 ≤ N := (CFC.sqrt_nonneg _).posSemidef.trace_nonneg
    have hb : N^2 ≤ K*v := hbound lam y hlam hlams hy
    have hNv : 2*N ≤ K+v := by nlinarith only [hb,hK,hv,hN,sq_nonneg (K-v)]
    obtain ⟨D,hD,hval⟩ := MatrixDual.trace_objective_approx
      (objectiveMatrix_posSemidef b O hlam) (cutMatrix_posSemidef c hy)
      (show 2*N < K+eta+v by linarith only [hNv,heta])
    refine ⟨D,hD,?_⟩
    have htr := trace_cutMatrix c y d D
    rw [trace_objectiveMatrix] at hval
    change (∑t,lam t*boundaryAverage b O t D) + (cutMatrix c y*D).trace < K+eta+v at hval
    linarith only [hval,htr])
  exact ⟨D,hD,hf,fun j => sub_neg.mp (hg j)⟩

lemma weighted_rows_bound (O : T → Finset E) (lam : T → ℝ) (a : E → ℝ)
    (hlam : ∀t, 0 ≤ lam t) (hsum : (∑t, lam t)=1) (ha : ∀e, 0 ≤ a e) :
    (∑e, Real.sqrt (∑t, if e ∈ O t then lam t / ((O t).card : ℝ) else 0)*a e)^2 ≤
      ∑t, (∑e ∈ O t, a e)^2/((O t).card : ℝ) := by
  let r : T → ℝ := fun t => Real.sqrt (lam t / ((O t).card : ℝ))
  let c : T → ℝ := fun t => (∑e ∈ O t, a e)/Real.sqrt ((O t).card : ℝ)
  have hw (e : E) : Real.sqrt (∑t, if e ∈ O t then lam t / ((O t).card : ℝ) else 0) ≤
      ∑t, if e ∈ O t then r t else 0 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨sum_nonneg (fun t _ => by split_ifs; exact Real.sqrt_nonneg _; exact le_rfl), ?_⟩
    calc
      (∑t, if e ∈ O t then lam t / ((O t).card : ℝ) else 0) =
          ∑t, (if e ∈ O t then r t else 0)^2 := by
        apply sum_congr rfl
        intro t _
        split_ifs
        · exact (Real.sq_sqrt (div_nonneg (hlam t) (Nat.cast_nonneg _))).symm
        · norm_num
      _ ≤ _ := sum_sq_le_sq_sum_of_nonneg (fun t _ => by split_ifs; exact Real.sqrt_nonneg _; exact le_rfl)
  have heq : (∑e, (∑t, if e ∈ O t then r t else 0)*a e) =
      ∑t, Real.sqrt (lam t)*c t := by
    simp_rw [sum_mul]
    rw [sum_comm]
    apply sum_congr rfl
    intro t _
    calc
      (∑e, (if e ∈ O t then r t else 0)*a e) = r t*∑e ∈ O t, a e := by
        rw [mul_sum]
        simp only [ite_mul,zero_mul]
        rw [←sum_filter]
        simp
      _ = Real.sqrt (lam t)*c t := by
        dsimp [r,c]
        rw [Real.sqrt_div (hlam t)]
        ring
  have hle := sum_le_sum (fun e (_ : e ∈ (univ : Finset E)) =>
    mul_le_mul_of_nonneg_right (hw e) (ha e))
  rw [heq] at hle
  have hsq := pow_le_pow_left₀ (sum_nonneg (fun e _ =>
    mul_nonneg (Real.sqrt_nonneg _) (ha e))) hle 2
  have hc := sum_mul_sq_le_sq_mul_sq univ (fun t => Real.sqrt (lam t)) c
  have hs : (∑t, (Real.sqrt (lam t))^2)=1 := by simpa only [Real.sq_sqrt (hlam _)] using hsum
  rw [hs,one_mul] at hc
  refine hsq.trans (hc.trans_eq ?_)
  apply sum_congr rfl
  intro t _
  simp only [c,div_pow,Real.sq_sqrt (Nat.cast_nonneg _)]

def edgeWeight (O : T → Finset E) (lam : T → ℝ) (e : E) : ℝ :=
  Real.sqrt (∑t, if e ∈ O t then lam t / ((O t).card : ℝ) else 0)

omit [Fintype V] [DecidableEq V] in
lemma objectiveMatrix_eq_sum_edges (b : E → V → ℝ) (O : T → Finset E) (lam : T → ℝ) :
    objectiveMatrix b O lam = ∑e, (∑t, if e ∈ O t then lam t / ((O t).card : ℝ) else 0) •
      vecMulVec (b e) (b e) := by
  have ht (t : T) : lam t • boundaryMatrix b O t =
      ∑e, (if e ∈ O t then lam t / ((O t).card : ℝ) else 0) • vecMulVec (b e) (b e) := by
    simp only [boundaryMatrix,smul_smul,div_eq_mul_inv,smul_sum,ite_smul,zero_smul]
    rw [←sum_filter]
    simp
  simp only [objectiveMatrix,ht]
  rw [sum_comm]
  simp only [sum_smul]

omit [Fintype V] [DecidableEq V] in
lemma weighted_gram (b : E → V → ℝ) (w : E → ℝ) :
    let B : Matrix V E ℝ := fun v e => b e v
    (B*diagonal w)*(B*diagonal w)ᵀ=∑e, (w e)^2 • vecMulVec (b e) (b e) := by
  dsimp
  ext i j
  change (∑e, ((Matrix.of (fun v e => b e v))*diagonal w) i e *
    ((Matrix.of (fun v e => b e v))*diagonal w) j e) = _
  simp only [mul_diagonal,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,vecMulVec_apply,Matrix.of_apply]
  apply sum_congr rfl
  intro e _
  ring

omit [Fintype V] [DecidableEq V] in
lemma objectiveMatrix_gram (b : E → V → ℝ) (O : T → Finset E) {lam : T → ℝ}
    (hlam : ∀t, 0 ≤ lam t) :
    let C : Matrix V E ℝ := (Matrix.of (fun v e => b e v))*diagonal (edgeWeight O lam)
    objectiveMatrix b O lam=C*Cᵀ := by
  dsimp
  rw [weighted_gram,objectiveMatrix_eq_sum_edges]
  apply sum_congr rfl
  intro e _
  have hp : 0 ≤ ∑t, if e ∈ O t then lam t / ((O t).card : ℝ) else 0 :=
    sum_nonneg (fun t _ => by split_ifs; exact div_nonneg (hlam t) (Nat.cast_nonneg _); exact le_rfl)
  rw [edgeWeight,Real.sq_sqrt hp]
  rfl

lemma nuclear_bound_of_embedding_bound (b : E → V → ℝ) (O : T → Finset E)
    {H : Type uH} [Fintype H] [DecidableEq H] (X : Matrix H V ℝ) {K : ℝ}
    (hbound : ∀U : Matrix E H ℝ, Uᵀ*U ≤ 1 → (∀e, 0 ≤ (U*(X*(Matrix.of (fun v e => b e v)))) e e) →
      (∑t, (∑e ∈ O t, (U*(X*(Matrix.of (fun v e => b e v)))) e e)^2/((O t).card : ℝ)) ≤ K)
    {lam : T → ℝ} (hlam : ∀t, 0 ≤ lam t) (hsum : (∑t, lam t)=1) :
    (CFC.sqrt (CFC.sqrt (Xᵀ*X)*objectiveMatrix b O lam*CFC.sqrt (Xᵀ*X))).trace^2 ≤ K := by
  let B : Matrix V E ℝ := fun v e => b e v
  let w := edgeWeight O lam
  have hw : ∀e, 0 ≤ w e := fun e => Real.sqrt_nonneg _
  obtain ⟨U,hU,hpos,htr⟩ := Polar.positive_optimizer (X*B) w hw
  rw [objectiveMatrix_gram b O hlam,Polar.dual_trace_rectangular]
  change (CFC.sqrt ((X*(B*diagonal w))*(X*(B*diagonal w))ᵀ)).trace^2 ≤ K
  rw [←Matrix.mul_assoc]
  have hsq := pow_le_pow_left₀ (CFC.sqrt_nonneg _).posSemidef.trace_nonneg htr 2
  exact hsq.trans ((weighted_rows_bound O lam (fun e => (U*(X*B)) e e) hlam hsum hpos).trans
    (hbound U hU hpos))

lemma sqrt_smul_real {A : Matrix V V ℝ} (hA : A.PosSemidef) {s : ℝ} (hs : 0 ≤ s) :
    CFC.sqrt (s • A)=Real.sqrt s • CFC.sqrt A := by
  apply CFC.sqrt_unique
  · simp only [smul_mul_assoc,mul_smul_comm,smul_smul,
      Real.mul_self_sqrt hs,CFC.sqrt_mul_sqrt_self A hA.nonneg]
  · exact ((CFC.sqrt_nonneg A).posSemidef.smul (Real.sqrt_nonneg s)).nonneg

lemma traceRoot_sq_smul {A Z : Matrix V V ℝ} (hA : A.PosSemidef) (hZ : Z.PosSemidef)
    {s : ℝ} (hs : 0 ≤ s) :
    (CFC.sqrt (CFC.sqrt (s • Z)*A*CFC.sqrt (s • Z))).trace^2 =
      s*(CFC.sqrt (CFC.sqrt Z*A*CFC.sqrt Z)).trace^2 := by
  have hp : (CFC.sqrt Z*A*CFC.sqrt Z).PosSemidef := by
    simpa only [(CFC.sqrt_nonneg Z).posSemidef.isHermitian.eq] using
      hA.conjTranspose_mul_mul_same (CFC.sqrt Z)
  rw [sqrt_smul_real hZ hs]
  simp only [smul_mul_assoc,mul_smul_comm,smul_smul,Real.mul_self_sqrt hs]
  rw [sqrt_smul_real hp hs,trace_smul]
  simp only [smul_eq_mul,mul_pow,Real.sq_sqrt hs]

lemma traceRoot_sq_tendsto {I : Type uI4} {l : Filter I} {A Z : Matrix V V ℝ}
    (hA : A.PosSemidef) (hZ : Z.PosSemidef) {g : I → Matrix V V ℝ}
    (hg : Tendsto g l (𝓝 Z)) (hgp : ∀ᶠ i in l, (g i).PosSemidef) :
    Tendsto (fun i => (CFC.sqrt (CFC.sqrt (g i)*A*CFC.sqrt (g i))).trace^2) l
      (𝓝 ((CFC.sqrt (CFC.sqrt Z*A*CFC.sqrt Z)).trace^2)) := by
  have h := MatrixDual.traceRoot_tendsto hA hZ tendsto_const_nhds hg
    (Eventually.of_forall (fun _ => hA)) hgp
  have hr := h.div_const 2
  simp only [mul_div_cancel_left₀ _ (show (2:ℝ) ≠ 0 by norm_num)] at hr
  exact hr.pow 2

omit [Fintype V] [DecidableEq V] in
lemma cutMatrix_smul (c : J → V → ℝ) (y : J → ℝ) (s : ℝ) :
    cutMatrix c (fun j => s*y j)=s • cutMatrix c y := by
  simp only [cutMatrix,smul_sum,smul_smul]

lemma trace_bound_of_nat_weights {A : Matrix V V ℝ} (hA : A.PosSemidef)
    (c : J → V → ℝ) (d : J → ℝ) (K : ℝ)
    (hb : ∀a : J → ℕ,
      (CFC.sqrt (CFC.sqrt (cutMatrix c (fun j => (a j : ℝ)))*A*
        CFC.sqrt (cutMatrix c (fun j => (a j : ℝ))))).trace^2 ≤ K*∑j, (a j : ℝ)*d j)
    {y : J → ℝ} (hy : ∀j, 0 ≤ y j) :
    (CFC.sqrt (CFC.sqrt (cutMatrix c y)*A*CFC.sqrt (cutMatrix c y))).trace^2 ≤
      K*∑j, y j*d j := by
  let a : ℝ → J → ℕ := fun t j => ⌊y j*t⌋₊
  let z : ℝ → J → ℝ := fun t j => (a t j : ℝ)/t
  have hz (j : J) : Tendsto (fun t => z t j) atTop (𝓝 (y j)) :=
    tendsto_nat_floor_mul_div_atTop (hy j)
  have hg : Tendsto (fun t => cutMatrix c (z t)) atTop (𝓝 (cutMatrix c y)) :=
    tendsto_finsetSum univ (fun j _ => (hz j).smul_const (vecMulVec (c j) (c j)))
  have hgp : ∀ᶠ t in atTop, (cutMatrix c (z t)).PosSemidef := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
    exact cutMatrix_posSemidef c (fun j => div_nonneg (Nat.cast_nonneg _) ht.le)
  have hl := traceRoot_sq_tendsto hA (cutMatrix_posSemidef c hy) hg hgp
  have hr : Tendsto (fun t => K*∑j, z t j*d j) atTop (𝓝 (K*∑j,y j*d j)) :=
    (tendsto_finsetSum univ (fun j _ => (hz j).mul_const (d j))).const_mul K
  apply le_of_tendsto_of_tendsto hl hr
  filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
  have heq : cutMatrix c (z t)=t⁻¹ • cutMatrix c (fun j => (a t j : ℝ)) := by
    simpa only [z,div_eq_mul_inv,mul_comm] using
      cutMatrix_smul c (fun j => (a t j : ℝ)) t⁻¹
  rw [heq,traceRoot_sq_smul hA (cutMatrix_posSemidef c (fun j => Nat.cast_nonneg _))
    (inv_nonneg.mpr ht.le)]
  have hh := mul_le_mul_of_nonneg_left (hb (a t)) (inv_nonneg.mpr ht.le)
  convert hh using 1
  simp only [z,div_eq_mul_inv,mul_sum]
  apply sum_congr rfl
  intro j _
  ring

def replicaMatrix (c : J → V → ℝ) (a : J → ℕ) :
    Matrix (Fin (Fintype.card (Σj, Fin (a j)))) V ℝ :=
  fun i v => c ((Fintype.equivFin (Σj, Fin (a j))).symm i).1 v

omit [Fintype V] [DecidableEq V] in
lemma replicaMatrix_binary (c : J → V → ℝ) (hc : ∀j v, c j v=0 ∨ c j v=1)
    (a : J → ℕ) : ∀i v, replicaMatrix c a i v=0 ∨ replicaMatrix c a i v=1 :=
  fun _i v => hc _ v

omit [Fintype V] [DecidableEq V] in
lemma replicaMatrix_gram (c : J → V → ℝ) (a : J → ℕ) :
    (replicaMatrix c a)ᵀ*replicaMatrix c a=cutMatrix c (fun j => (a j : ℝ)) := by
  ext v w
  change (∑i, c ((Fintype.equivFin (Σj, Fin (a j))).symm i).1 v *
    c ((Fintype.equivFin (Σj, Fin (a j))).symm i).1 w) = _
  rw [(Fintype.equivFin (Σj, Fin (a j))).symm.sum_comp
    (fun i : (Σj, Fin (a j)) => c i.1 v*c i.1 w)]
  simp only [Fintype.sum_sigma,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    cutMatrix,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,vecMulVec_apply]

omit [DecidableEq V] [DecidableEq E] in
lemma replicaMatrix_energy (b : E → V → ℝ) (c : J → V → ℝ) (a : J → ℕ) :
    (∑e, ∑i, (replicaMatrix c a * Matrix.of (fun v e => b e v)) i e ^ 2) =
      ∑j, (a j : ℝ)*(∑e, (∑v, c j v*b e v)^2) := by
  rw [sum_comm]
  change (∑i, (fun j : (Σj, Fin (a j)) => ∑e, (∑v, c j.1 v*b e v)^2)
    ((Fintype.equivFin (Σj, Fin (a j))).symm i)) = _
  rw [(Fintype.equivFin (Σj, Fin (a j))).symm.sum_comp
    (fun j : (Σj, Fin (a j)) => ∑e, (∑v, c j.1 v*b e v)^2)]
  simp only [Fintype.sum_sigma,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

lemma shortcut_of_binary_bound (b : E → V → ℝ) (O : T → Finset E)
    (c : J → V → ℝ) (d : J → ℝ) (hc : ∀j v, c j v=0 ∨ c j v=1)
    (hd : ∀j, 0 < d j) (henergy : ∀j, (∑e, (∑v, c j v*b e v)^2)=d j)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀h : ℕ, ∀X : Matrix (Fin h) V ℝ, (∀i v, X i v=0 ∨ X i v=1) →
      ∀U : Matrix E (Fin h) ℝ, Uᵀ*U ≤ 1 →
      (∀e, 0 ≤ (U*(X*Matrix.of (fun v e => b e v))) e e) →
      (∑t, (∑e ∈ O t, (U*(X*Matrix.of (fun v e => b e v))) e e)^2/((O t).card : ℝ)) ≤
        K*(∑e, ∑i, (X*Matrix.of (fun v e => b e v)) i e ^2))
    {eta : ℝ} (heta : 0 < eta) :
    ∃D : Matrix V V ℝ, D.PosDef ∧
      (∀t, boundaryAverage b O t D < K+eta) ∧ (∀j, c j ⬝ᵥ (D *ᵥ c j) < d j) := by
  apply shortcut_of_trace_bound b O c d hd hK _ heta
  intro lam y hlam hlams hy
  apply trace_bound_of_nat_weights (objectiveMatrix_posSemidef b O hlam) c d K _ hy
  intro a
  have heq := nuclear_bound_of_embedding_bound b O (replicaMatrix c a)
    (hbound _ _ (replicaMatrix_binary c hc a)) hlam hlams
  rwa [replicaMatrix_gram,replicaMatrix_energy,show
    (∑j, (a j : ℝ)*(∑ e, (∑ v, c j v*b e v)^2))=∑j, (a j : ℝ)*d j by simp_rw [henergy]] at heq

end
end StrongThinTree.ShortcutDual

end

end OAI
