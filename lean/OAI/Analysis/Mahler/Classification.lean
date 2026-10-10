import OAI.Analysis.Mahler.Splitting

namespace OAI

noncomputable section

namespace SymmetricMahler

open Set Metric

section
variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

structure LDecomposition where
  left : Submodule ℝ E
  right : Submodule ℝ E
  equiv : (left × right) ≃ₗ[ℝ] E
  norm_add : ∀ z, ‖equiv z‖ = ‖z.1‖ + ‖z.2‖
  left_pos : 0 < Module.finrank ℝ left
  right_pos : 0 < Module.finrank ℝ right

variable {E} [FiniteDimensional ℝ E] [Nontrivial E]

lemma maximal_unit_face_hull (hmed : HasMetricMedians E) {K : Set E}
    (hK : IsMaximalProperFace (closedBall (0:E) 1) K) (hn : K.Nonempty) :
    closedBall (0:E) 1 = convexHull ℝ (K ∪ -K) := by
  apply subset_antisymm
  · rw [unitBall_eq_convexHull_extreme hmed]
    apply convexHull_mono
    intro x hx
    rcases maximal_unit_face_vertex_sign hmed hK hn hx with hh | hh
    · exact Or.inl hh
    · exact Or.inr (by simpa using hh)
  · apply convexHull_min _ (convex_closedBall _ _)
    rintro x (hx | hx)
    · exact hK.1.subset hx
    · have hx' : -x ∈ K := by simpa using hx
      simpa using hK.1.subset hx'

lemma norm_add_of_split (hmed : HasMetricMedians E) {K F G : Set E}
    (hK : IsMaximalProperFace (closedBall (0:E) 1) K)
    (p : IsSplitPair K F G) (hFn : F.Nonempty) (hGn : G.Nonempty) :
    Nonempty (LDecomposition E) := by
  let U := Submodule.span ℝ F
  let V := Submodule.span ℝ G
  have hKn := hFn.mono p.1.1.subset
  have hsup : U ⊔ V = ⊤ := by
    apply top_unique
    rw [← maximal_unit_face_span hmed hK hKn]
    apply Submodule.span_le.mpr
    rw [p.1.2.2.2]
    apply convexHull_min _ (Submodule.convex _)
    exact union_subset (fun _ hx => (show U ≤ U ⊔ V from le_sup_left) (Submodule.subset_span hx))
      (fun _ hx => (show V ≤ U ⊔ V from le_sup_right) (Submodule.subset_span hx))
  have hcompl : IsCompl U V := ⟨p.2,codisjoint_iff.mpr hsup⟩
  let e := Submodule.prodEquivOfIsCompl U V hcompl
  let C : Set E := {x | ‖(e.symm x).1‖+‖(e.symm x).2‖ ≤ 1}
  have hC : Convex ℝ C := by
    intro x hx y hy a b ha hb hab
    change ‖(e.symm (a • x+b • y)).1‖+‖(e.symm (a • x+b • y)).2‖ ≤ 1
    simp only [map_add,map_smul,Prod.fst_add,Prod.smul_fst,Prod.snd_add,Prod.smul_snd]
    have h1 := norm_add_le (a • (e.symm x).1) (b • (e.symm y).1)
    have h2 := norm_add_le (a • (e.symm x).2) (b • (e.symm y).2)
    simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg ha,abs_of_nonneg hb] at h1 h2
    have h3 := mul_le_mul_of_nonneg_left hx ha
    have h4 := mul_le_mul_of_nonneg_left hy hb
    change a * (‖(e.symm x).1‖+‖(e.symm x).2‖) ≤ a*1 at h3
    change b * (‖(e.symm y).1‖+‖(e.symm y).2‖) ≤ b*1 at h4
    nlinarith
  have hFC : F ⊆ C := by
    intro x hx
    have he : e.symm x = (⟨x,Submodule.subset_span hx⟩,0) :=
      Submodule.prodEquivOfIsCompl_symm_apply_left U V hcompl ⟨x,Submodule.subset_span hx⟩
    change ‖(e.symm x).1‖+‖(e.symm x).2‖ ≤ 1
    rw [he]
    simpa using mem_closedBall_zero_iff.mp (hK.1.subset (p.1.1.subset hx))
  have hGC : G ⊆ C := by
    intro x hx
    have he : e.symm x = (0,⟨x,Submodule.subset_span hx⟩) :=
      Submodule.prodEquivOfIsCompl_symm_apply_right U V hcompl ⟨x,Submodule.subset_span hx⟩
    change ‖(e.symm x).1‖+‖(e.symm x).2‖ ≤ 1
    rw [he]
    simpa using mem_closedBall_zero_iff.mp (hK.1.subset (p.1.2.1.subset hx))
  have hKC : K ⊆ C := by
    rw [p.1.2.2.2]
    exact convexHull_min (union_subset hFC hGC) hC
  have hBC : closedBall (0:E) 1 ⊆ C := by
    rw [maximal_unit_face_hull hmed hK hKn]
    apply convexHull_min _ hC
    rintro x (hx | hx)
    · exact hKC hx
    · have hh := hKC (show -x ∈ K by simpa using hx)
      simpa [C] using hh
  have heNorm : ∀ z, ‖e z‖ = ‖z.1‖+‖z.2‖ := by
    intro z
    apply le_antisymm
    · exact norm_add_le (z.1:E) (z.2:E)
    · by_cases hz : e z = 0
      · have hz' : z=0 := e.injective (by simpa using hz)
        simp [hz']
      have hp : 0 < ‖e z‖ := norm_pos_iff.mpr hz
      have hx : ‖e z‖⁻¹ • e z ∈ closedBall (0:E) 1 := by
        rw [mem_closedBall_zero_iff,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hp)]
        simp [hp.ne']
      have hh := hBC hx
      change ‖(e.symm (‖e z‖⁻¹ • e z)).1‖+‖(e.symm (‖e z‖⁻¹ • e z)).2‖ ≤ 1 at hh
      simp only [map_smul,e.symm_apply_apply,Prod.smul_fst,Prod.smul_snd,norm_smul,
        Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hp)] at hh
      have hh' : (‖z.1‖+‖z.2‖) / ‖e z‖ ≤ 1 := by
        simpa only [div_eq_mul_inv,mul_add,add_mul,mul_comm] using hh
      exact (div_le_one hp).mp hh'
  exact ⟨⟨U,V,e,heNorm,(hK.1.trans p.1.1).rank_pos hmed
    (proper_unit_face_subface_ne hK.1 hK.2.1 p.1.1.subset) hFn,
    (hK.1.trans p.1.2.1).rank_pos hmed
    (proper_unit_face_subface_ne hK.1 hK.2.1 p.1.2.1.subset) hGn⟩⟩

end

section

lemma HasMetricMedians.of_retract {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (h : HasMetricMedians X) (i : Y → X) (p : X → Y)
    (hi : ∀ a b, dist (i a) (i b) ≤ dist a b)
    (hp : ∀ a b, dist (p a) (p b) ≤ dist a b)
    (hpi : ∀ a, p (i a)=a) : HasMetricMedians Y := by
  have he : ∀ a b, dist (i a) (i b)=dist a b := by
    intro a b
    exact le_antisymm (hi a b) (by simpa [hpi] using hp (i a) (i b))
  intro x
  obtain ⟨m,hm⟩ := h (i ∘ x)
  refine ⟨p m,fun a b hab => ?_⟩
  have h1 := hp (i (x a)) m
  have h2 := hp m (i (x b))
  have h3 := hm a b hab
  simp only [Function.comp_apply,he] at h3
  simp only [hpi] at h1 h2
  have h4 := dist_triangle (x a) (p m) (x b)
  linarith

lemma HasMetricMedians.linearIsometryEquiv {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (h : HasMetricMedians E) (e : E ≃ₗᵢ[ℝ] F) : HasMetricMedians F := by
  exact h.of_retract e.symm e (fun a b => (e.symm.dist_map a b).le)
    (fun a b => (e.dist_map a b).le) e.apply_symm_apply

lemma continuousLinearMap_dist_le {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (p : E →L[ℝ] F) (hp : ∀ x, ‖p x‖ ≤ ‖x‖) (a b : E) :
    dist (p a) (p b) ≤ dist a b := by
  simpa only [dist_eq_norm,map_sub] using hp (a-b)

lemma dual_comp_dist_le {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (p : E →L[ℝ] F) (hp : ∀ x, ‖p x‖ ≤ ‖x‖) (a b : F →L[ℝ] ℝ) :
    dist (a.comp p) (b.comp p) ≤ dist a b := by
  have hpn : ‖p‖ ≤ 1 := p.opNorm_le_bound zero_le_one (by simpa using hp)
  have hh := (a-b).opNorm_comp_le p
  have hh' := mul_le_mul_of_nonneg_left hpn (norm_nonneg (a-b))
  rw [dist_eq_norm,dist_eq_norm]
  calc
    ‖a.comp p-b.comp p‖ = ‖(a-b).comp p‖ := by rfl
    _ ≤ ‖a-b‖*‖p‖ := hh
    _ ≤ ‖a-b‖ := by simpa using hh'

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E]

namespace LDecomposition
variable (d : LDecomposition E)

def swap : LDecomposition E where
  left := d.right
  right := d.left
  equiv := (LinearEquiv.prodComm ℝ d.right d.left).trans d.equiv
  norm_add := fun z => by simpa [add_comm,Prod.swap] using d.norm_add (z.2,z.1)
  left_pos := d.right_pos
  right_pos := d.left_pos

lemma finrank_add : Module.finrank ℝ d.left + Module.finrank ℝ d.right = Module.finrank ℝ E := by
  rw [← Module.finrank_prod]
  exact d.equiv.finrank_eq

lemma left_lt : Module.finrank ℝ d.left < Module.finrank ℝ E := by
  have := d.finrank_add
  have := d.right_pos
  omega

lemma right_lt : Module.finrank ℝ d.right < Module.finrank ℝ E := by
  have := d.finrank_add
  have := d.left_pos
  omega

def leftInclusion : d.left →L[ℝ] E :=
  LinearMap.toContinuousLinearMap (d.equiv.toLinearMap.comp (LinearMap.inl ℝ d.left d.right))

def leftProjection : E →L[ℝ] d.left :=
  LinearMap.toContinuousLinearMap ((LinearMap.fst ℝ d.left d.right).comp d.equiv.symm.toLinearMap)

@[simp] lemma leftProjection_leftInclusion (x : d.left) :
    d.leftProjection (d.leftInclusion x)=x := by
  change (d.equiv.symm (d.equiv (x,0))).1=x
  simp

lemma norm_leftInclusion (x : d.left) : ‖d.leftInclusion x‖ = ‖x‖ := by
  change ‖d.equiv (x,0)‖=‖x‖
  simpa using d.norm_add (x,0)

lemma norm_leftProjection_le (x : E) : ‖d.leftProjection x‖ ≤ ‖x‖ := by
  have he := d.norm_add (d.equiv.symm x)
  rw [d.equiv.apply_symm_apply] at he
  change ‖(d.equiv.symm x).1‖ ≤ ‖x‖
  linarith [norm_nonneg (d.equiv.symm x).2]

lemma left_medians (h : HasMetricMedians E) : HasMetricMedians d.left :=
  h.of_retract d.leftInclusion d.leftProjection
    (continuousLinearMap_dist_le _ (fun x => (d.norm_leftInclusion x).le))
    (continuousLinearMap_dist_le _ d.norm_leftProjection_le) d.leftProjection_leftInclusion

lemma left_dual_medians (h : HasMetricMedians (E →L[ℝ] ℝ)) :
    HasMetricMedians (d.left →L[ℝ] ℝ) := by
  apply h.of_retract (fun f => f.comp d.leftProjection) (fun f => f.comp d.leftInclusion)
  · exact dual_comp_dist_le _ d.norm_leftProjection_le
  · exact dual_comp_dist_le _ (fun x => (d.norm_leftInclusion x).le)
  · intro f
    ext x
    simp

lemma right_medians (h : HasMetricMedians E) : HasMetricMedians d.right :=
  d.swap.left_medians h

lemma right_dual_medians (h : HasMetricMedians (E →L[ℝ] ℝ)) :
    HasMetricMedians (d.right →L[ℝ] ℝ) := d.swap.left_dual_medians h
end LDecomposition

end

section

def HannerSpace (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] : Prop :=
  ∃ (n : ℕ) (H : Set (Fin n → ℝ)), IsHanner H ∧
    ∃ e : (Fin n → ℝ) ≃ₗ[ℝ] E, closedBall (0:E) 1 = e '' H

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma HannerSpace.linearIsometryEquiv (h : HannerSpace E) (e : E ≃ₗᵢ[ℝ] F) :
    HannerSpace F := by
  obtain ⟨n,H,hH,f,hf⟩ := h
  refine ⟨n,H,hH,f.trans e.toLinearEquiv,?_⟩
  change closedBall (0:F) 1 = (fun x => e (f x)) '' H
  rw [← image_image,← hf,e.image_closedBall,map_zero]

lemma hannerSpace_one [FiniteDimensional ℝ E] (hd : Module.finrank ℝ E = 1) :
    HannerSpace E := by
  let e : (Fin 1 → ℝ) ≃ₗ[ℝ] E := LinearEquiv.ofFinrankEq _ _ (by simpa using hd.symm)
  let u : Fin 1 → ℝ := fun _ => 1
  have hu : e u ≠ 0 := by
    intro hh
    have : u=0 := e.injective (by simpa using hh)
    have hh := congrFun this 0
    norm_num [u] at hh
  have hp : 0 < ‖e u‖ := norm_pos_iff.mpr hu
  have he (x : Fin 1 → ℝ) : ‖e x‖ = |x 0| * ‖e u‖ := by
    have hx : x = x 0 • u := by ext i; fin_cases i; simp [u]
    conv_lhs => rw [hx]
    rw [map_smul,norm_smul,Real.norm_eq_abs]
  refine ⟨1,_,IsHanner.interval (‖e u‖⁻¹) (inv_pos.mpr hp),e,?_⟩
  ext y
  obtain ⟨x,rfl⟩ := e.surjective y
  rw [e.injective.mem_set_image,mem_closedBall_zero_iff,he]
  simp only [mem_Icc,Pi.le_def,Fin.forall_fin_one]
  rw [← abs_le,← one_div]
  exact (le_div_iff₀ hp).symm

def coordinateDual {n : ℕ} [FiniteDimensional ℝ E] (e : (Fin n → ℝ) ≃ₗ[ℝ] E) :
    (Fin n → ℝ) ≃ₗ[ℝ] (E →L[ℝ] ℝ) :=
  (((Pi.basisFun ℝ (Fin n)).toDualEquiv).trans e.symm.dualMap).trans
    LinearMap.toContinuousLinearMap

lemma coordinateDual_apply {n : ℕ} [FiniteDimensional ℝ E]
    (e : (Fin n → ℝ) ≃ₗ[ℝ] E) (p x : Fin n → ℝ) :
    coordinateDual e p (e x) = ∑ i, p i*x i := by
  let f : (Fin n → ℝ) →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap ((Pi.basisFun ℝ (Fin n)).toDual p)
  have hc (i : Fin n) : f (Pi.single i 1) = p i := by
    simpa [f] using (Pi.basisFun ℝ (Fin n)).toDual_apply_left p i
  have hh := pairing_of_dual f x
  simp only [hc] at hh
  change (Pi.basisFun ℝ (Fin n)).toDual p (e.symm (e x)) = _
  rw [e.symm_apply_apply]
  exact hh.symm

lemma dual_norm_le_one_iff (f : E →L[ℝ] ℝ) :
    ‖f‖ ≤ 1 ↔ ∀ x ∈ closedBall (0:E) 1, f x ≤ 1 := by
  constructor
  · intro hf x hx
    have hxn := mem_closedBall_zero_iff.mp hx
    exact (le_abs_self (f x)).trans <| (f.le_opNorm x).trans <|
      (mul_le_mul hf hxn (norm_nonneg x) zero_le_one).trans_eq (mul_one 1)
  · intro hf
    apply ContinuousLinearMap.opNorm_le_of_unit_norm zero_le_one
    intro x hx
    rw [Real.norm_eq_abs,abs_le]
    have hh := hf (-x) (by simp [hx])
    simpa using And.intro (by linarith [show f (-x) = -f x from map_neg f x])
      (hf x (by simp [hx]))

lemma HannerSpace.dual [FiniteDimensional ℝ E] (h : HannerSpace E) :
    HannerSpace (E →L[ℝ] ℝ) := by
  obtain ⟨n,H,hH,e,he⟩ := h
  refine ⟨n,coordinatePolar H,hH.polar,coordinateDual e,?_⟩
  ext f
  obtain ⟨p,rfl⟩ := (coordinateDual e).surjective f
  rw [(coordinateDual e).injective.mem_set_image,mem_closedBall_zero_iff,
    dual_norm_le_one_iff,he]
  constructor
  · intro hh x hx
    simpa only [coordinateDual_apply] using hh (e x) (mem_image_of_mem e hx)
  · intro hh y hy
    obtain ⟨x,hx,rfl⟩ := hy
    simpa only [coordinateDual_apply] using hh x hx

end

section

def normData (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] : RealNormData E where
  toAddGroupNorm := normAddGroupNorm E
  smul_eq := fun a x => by
    change ‖a • x‖ = |a| * ‖x‖
    simpa only [Real.norm_eq_abs] using norm_smul a x

@[simp] lemma normData_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : E) : normData E x = ‖x‖ := rfl

lemma normData_unit (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    (normData E).unit = closedBall (0:E) 1 := by
  ext x
  exact mem_closedBall_zero_iff.symm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma LDecomposition.unitBall (d : LDecomposition E) :
    closedBall (0:E) 1 = d.equiv '' convexHull ℝ
      (((fun x : d.left => (x,(0:d.right))) '' closedBall (0:d.left) 1) ∪
        ((fun y : d.right => ((0:d.left),y)) '' closedBall (0:d.right) 1)) := by
  rw [← normData_unit d.left,← normData_unit d.right,← RealNormData.unit_sum]
  ext x
  obtain ⟨z,rfl⟩ := d.equiv.surjective x
  rw [d.equiv.injective.mem_set_image,mem_closedBall_zero_iff,d.norm_add]
  rfl

lemma LDecomposition.hannerSpace (d : LDecomposition E)
    (hU : HannerSpace d.left) (hV : HannerSpace d.right) : HannerSpace E := by
  obtain ⟨k,A,hA,eu,heu⟩ := hU
  obtain ⟨l,B,hB,ev,hev⟩ := hV
  let e : (Fin (k+l) → ℝ) ≃ₗ[ℝ] E :=
    (appendEquiv k l).symm.trans ((eu.prodCongr ev).trans d.equiv)
  have h1 (x : Fin k → ℝ) : e (Fin.append x 0) = d.equiv (eu x,0) := by
    change d.equiv ((eu.prodCongr ev) ((appendEquiv k l).symm (appendEquiv k l (x,0)))) = _
    rw [(appendEquiv k l).symm_apply_apply]
    simp
  have h2 (y : Fin l → ℝ) : e (Fin.append 0 y) = d.equiv (0,ev y) := by
    change d.equiv ((eu.prodCongr ev) ((appendEquiv k l).symm (appendEquiv k l (0,y)))) = _
    rw [(appendEquiv k l).symm_apply_apply]
    simp
  refine ⟨k+l,hannerJoin A B,IsHanner.join hA hB,e,?_⟩
  rw [d.unitBall,heu,hev]
  change d.equiv.toLinearMap '' convexHull ℝ _ = e.toLinearMap '' convexHull ℝ _
  rw [LinearMap.image_convexHull,LinearMap.image_convexHull]
  congr 1
  simp only [image_union,image_image]
  congr 1
  · congr 1
    funext x
    exact (h1 x).symm
  · congr 1
    funext y
    exact (h2 y).symm

end

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E] [Nontrivial E]

theorem median_decomposition (hmed : HasMetricMedians E)
    (hdual : HasMetricMedians (E →L[ℝ] ℝ)) (hdim : 2 ≤ Module.finrank ℝ E) :
    Nonempty (LDecomposition E) ∨ Nonempty (LDecomposition (E →L[ℝ] ℝ)) := by
  classical
  by_cases hd2 : Module.finrank ℝ E = 2
  · obtain ⟨K,hK,hKn⟩ := exists_maximal_unit_face hmed
    have hr : faceRank K = 2 := (maximal_unit_face_rank hmed hK hKn).trans hd2
    obtain ⟨F,G,p,-,-,hFn,hGn⟩ := face_rank_two_pair hmed hK.1 hK.2.1 hr
    exact Or.inl (norm_add_of_split hmed hK p hFn hGn)
  by_cases hh : ∃ K, IsMaximalProperFace (closedBall (0:E) 1) K ∧ HasMFaceStructure K
  · obtain ⟨K,hK,hmK⟩ := hh
    have hbi : HasMetricMedians ((E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
      HasMetricMedians.linearIsometryEquiv (E:=E) (F:=((E →L[ℝ] ℝ) →L[ℝ] ℝ))
        hmed (finiteBidual (E:=E))
    have hn : ∀ L, IsMaximalProperFace (closedBall (0 : E →L[ℝ] ℝ) 1) L →
        ¬ HasMFaceStructure L := by
      intro L hL hmL
      exact not_primal_dual_maximal_mfaces hmed hdual (by omega) hK hmK hL hmL
    obtain ⟨L,F,G,hL,p,hFn,hGn⟩ := proper_split_of_no_maximal_mface hdual hbi
      (by rwa [finrank_strongDual]) hn
    exact Or.inr (norm_add_of_split hdual hL p hFn hGn)
  · have hn : ∀ K, IsMaximalProperFace (closedBall (0:E) 1) K → ¬ HasMFaceStructure K := by
      intro K hK hmK
      exact hh ⟨K,hK,hmK⟩
    obtain ⟨K,F,G,hK,p,hFn,hGn⟩ := proper_split_of_no_maximal_mface hmed hdual hdim hn
    exact Or.inl (norm_add_of_split hmed hK p hFn hGn)

end
section

universe u

private theorem hannerSpace_of_medians_rank (n : ℕ) :
    ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [Nontrivial E], Module.finrank ℝ E = n →
      HasMetricMedians E → HasMetricMedians (E →L[ℝ] ℝ) → HannerSpace E := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro E _ _ _ _ he hmed hdual
    by_cases hn : n = 1
    · exact hannerSpace_one (he.trans hn)
    have hp : 0 < Module.finrank ℝ E := Module.finrank_pos
    have hd : 2 ≤ Module.finrank ℝ E := by omega
    rcases median_decomposition hmed hdual hd with hd | hd
    · obtain ⟨d⟩ := hd
      let : Nontrivial d.left := Module.finrank_pos_iff.mp d.left_pos
      let : Nontrivial d.right := Module.finrank_pos_iff.mp d.right_pos
      apply d.hannerSpace
      · exact ih _ (by have := d.left_lt; omega) d.left rfl
          (d.left_medians hmed) (d.left_dual_medians hdual)
      · exact ih _ (by have := d.right_lt; omega) d.right rfl
          (d.right_medians hmed) (d.right_dual_medians hdual)
    · obtain ⟨d⟩ := hd
      let : Nontrivial d.left := Module.finrank_pos_iff.mp d.left_pos
      let : Nontrivial d.right := Module.finrank_pos_iff.mp d.right_pos
      have hbi : HasMetricMedians ((E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
        HasMetricMedians.linearIsometryEquiv (E:=E) (F:=((E →L[ℝ] ℝ) →L[ℝ] ℝ))
          hmed (finiteBidual (E:=E))
      have he' : Module.finrank ℝ (E →L[ℝ] ℝ) = n := finrank_strongDual.trans he
      have hh : HannerSpace (E →L[ℝ] ℝ) := d.hannerSpace
        (ih _ (by have := d.left_lt; omega) d.left rfl
          (d.left_medians hdual) (d.left_dual_medians hbi))
        (ih _ (by have := d.right_lt; omega) d.right rfl
          (d.right_medians hdual) (d.right_dual_medians hbi))
      exact HannerSpace.linearIsometryEquiv (E:=((E →L[ℝ] ℝ) →L[ℝ] ℝ)) (F:=E)
        hh.dual (finiteBidual (E:=E)).symm

theorem hannerSpace_of_medians {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E]
    (hmed : HasMetricMedians E) (hdual : HasMetricMedians (E →L[ℝ] ℝ)) : HannerSpace E :=
  hannerSpace_of_medians_rank _ E rfl hmed hdual

namespace RealNormData

lemma coordinateDual_space_apply {n : ℕ} (g : RealNormData (Fin n → ℝ))
    (p : Fin n → ℝ) (x : g.Space) :
    coordinateDual g.spaceEquiv.symm p x = ∑ i, p i*(g.spaceEquiv x) i := by
  have hh := coordinateDual_apply g.spaceEquiv.symm p (g.spaceEquiv x)
  simpa using hh

def IsDual.dualIsometry {n : ℕ} {g h : RealNormData (Fin n → ℝ)} (hd : g.IsDual h) :
    h.Space ≃ₗᵢ[ℝ] (g.Space →L[ℝ] ℝ) where
  toLinearEquiv := h.spaceEquiv.trans (coordinateDual g.spaceEquiv.symm)
  norm_map' := by
    intro p
    change ‖coordinateDual g.spaceEquiv.symm (h.spaceEquiv p)‖ = h (h.spaceEquiv p)
    let f := coordinateDual g.spaceEquiv.symm (h.spaceEquiv p)
    have he (x : g.Space) : f x = ∑ i, (h.spaceEquiv p) i*(g.spaceEquiv x) i :=
      coordinateDual_space_apply g _ x
    apply le_antisymm
    · apply ContinuousLinearMap.opNorm_le_bound _ (h.nonneg _)
      intro x
      rw [Real.norm_eq_abs,abs_le]
      have h1 := hd.1 (g.spaceEquiv x) (h.spaceEquiv p)
      have h2 := hd.1 (-g.spaceEquiv x) (h.spaceEquiv p)
      rw [← he x] at h1
      have he2 : (∑ i, (h.spaceEquiv p) i*(-g.spaceEquiv x) i) = -f x := by
        rw [he]
        simp only [Pi.neg_apply,mul_neg,Finset.sum_neg_distrib]
      rw [he2,g.apply_neg] at h2
      rw [space_norm]
      constructor <;> nlinarith
    · obtain ⟨x,hx,hxp⟩ := hd.2 (h.spaceEquiv p)
      have hx' : ‖g.spaceEquiv.symm x‖ ≤ 1 := by
        change g x ≤ 1 at hx
        simpa only [space_norm,g.spaceEquiv.apply_symm_apply] using hx
      have hh := (le_abs_self (f (g.spaceEquiv.symm x))).trans ((f.le_opNorm _).trans
        ((mul_le_mul_of_nonneg_left hx' (norm_nonneg f)).trans_eq (mul_one _)))
      rw [he] at hh
      simpa only [g.spaceEquiv.apply_symm_apply,hxp] using hh

lemma hannerSpace_iff_linearHanner {n : ℕ} (g : RealNormData (Fin n → ℝ)) :
    HannerSpace g.Space ↔ IsLinearHanner g.unit := by
  constructor
  · rintro ⟨m,H,hH,e,he⟩
    have hmn : m=n := by simpa using (e.trans g.spaceEquiv).finrank_eq
    subst m
    refine ⟨H,hH,e.trans g.spaceEquiv,?_⟩
    rw [g.unit_eq_image_closedBall,he,image_image]
    rfl
  · rintro ⟨H,hH,e,he⟩
    refine ⟨n,H,hH,e.trans g.spaceEquiv.symm,?_⟩
    apply (Set.image_injective.mpr g.spaceEquiv.injective)
    rw [← g.unit_eq_image_closedBall,he,image_image]
    congr 1

end RealNormData
end

open Set MeasureTheory Metric

theorem equality_implies_linearHanner {n : ℕ} (hn : 1 ≤ n)
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hsym : ∀ x ∈ K, -x ∈ K) (hint : (interior K).Nonempty)
    (heq : (volume K).toReal * (volume (coordinatePolar K)).toReal =
      (4 : ℝ)^n / (Nat.factorial n : ℝ)) : IsLinearHanner K := by
  obtain ⟨g,h,hg,-,hd,hmh,hmg⟩ :=
    equality_polar_gauge_medians hn hK hconv hsym hint heq
  have hdim : Module.finrank ℝ g.Space = n := by simpa using g.spaceEquiv.finrank_eq
  have hpos : 0 < Module.finrank ℝ g.Space := by omega
  let : Nontrivial g.Space := Module.finrank_pos_iff.mp hpos
  have hdual : HasMetricMedians (g.Space →L[ℝ] ℝ) :=
    HasMetricMedians.linearIsometryEquiv (E:=h.Space) (F:=(g.Space →L[ℝ] ℝ))
      hmh hd.dualIsometry
  rw [← hg]
  exact (g.hannerSpace_iff_linearHanner).mp (hannerSpace_of_medians hmg hdual)

theorem symmetric_mahler_equality {n : ℕ} (hn : 1 ≤ n)
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hsym : ∀ x ∈ K, -x ∈ K) (hint : (interior K).Nonempty) :
    ((volume K).toReal * (volume (coordinatePolar K)).toReal =
      (4 : ℝ)^n / (Nat.factorial n : ℝ)) ↔ IsLinearHanner K := by
  exact ⟨equality_implies_linearHanner hn hK hconv hsym hint,
    IsLinearHanner.volumeProduct⟩

end SymmetricMahler

end

end OAI
