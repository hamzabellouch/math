import OAI.Analysis.TreePotential.StartRepresentation

namespace OAI

noncomputable section
open Set
open scoped ENNReal
open Set Filter Topology
open scoped Classical

namespace BoundedTreePotentials.Segments

lemma exists_costDomain_approx (x : DualCore) {e : ℝ} (he : 0< e) :
    ∃ a : CostDomain,representationCost a.val≤ ENNReal.ofReal ‖x‖ ∧
      ‖representationMap a-x‖≤ e := by
  obtain ⟨a,ha,hc,he'⟩ := exists_representation_approx x he
  exact ⟨⟨a,ha⟩,hc,he'⟩

/-- Reverse literal representation theorem. The geometric residual expansion
is a single countable signed segment array with the original recursive cost;
no attained infimum or finite-support restriction is assumed. -/
theorem exists_representation_near_norm (x : DualCore) {e : ℝ} (he : 0< e) :
    ∃ (a : Segment → ℝ) (ha : representationCost a≠∞),
      representedCore a ha=x ∧ (representationCost a).toReal<‖x‖+e := by
  let δ : ℕ → ℝ := fun n => e/4*(1/2:ℝ)^n
  have hδpos (n : ℕ) : 0<δ n := by dsimp [δ]; positivity
  have hδsum : Summable δ := summable_geometric_two.mul_left (e/4)
  have hδtsum : (∑' n,δ n)=e/2 := by
    rw [show δ=(fun n => e/4*(1/2:ℝ)^n) from rfl,tsum_mul_left,tsum_geometric_two]
    ring
  choose b hb using fun (z : DualCore) (n : ℕ) => exists_costDomain_approx z (hδpos n)
  let r : ℕ → DualCore := fun n => Nat.rec x (fun n z => z-representationMap (b z n)) n
  let a : ℕ → CostDomain := fun n => b (r n) n
  have hr0 : r 0=x := rfl
  have hrstep (n : ℕ) : r (n+1)=r n-representationMap (a n) := rfl
  have hrcost (n : ℕ) : representationCost (a n).val≤ ENNReal.ofReal ‖r n‖ := (hb (r n) n).1
  have hrsmall (n : ℕ) : ‖r (n+1)‖≤δ n := by
    rw [hrstep,norm_sub_rev]
    exact (hb (r n) n).2
  have hcostbound : (∑' n,representationCost (a n).val) ≤ ENNReal.ofReal (‖x‖+e/2) := by
    rw [tsum_eq_zero_add' ENNReal.summable]
    calc
      _ ≤ ENNReal.ofReal ‖x‖+∑' n,ENNReal.ofReal (δ n) := by
        apply add_le_add (by simpa only [hr0] using hrcost 0)
        exact ENNReal.tsum_le_tsum (fun n => (hrcost (n+1)).trans (ENNReal.ofReal_le_ofReal (hrsmall n)))
      _ = _ := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => (hδpos n).le) hδsum,hδtsum,
          ENNReal.ofReal_add (norm_nonneg x) (by positivity)]
  have hcost : (∑' n,representationCost (a n).val)≠∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hcostbound
  have hnorm : Summable (fun n => ‖representationMap (a n)‖) := by
    apply Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => representedCore_norm (a n).val (a n).property)
    exact ENNReal.summable_toReal hcost
  have hrtend : Tendsto r atTop (𝓝 0) := by
    apply (tendsto_add_atTop_iff_nat 1).mp
    apply squeeze_zero_norm hrsmall
    have hh := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2)
      (by norm_num : (1/2:ℝ)<1)).const_mul (e/4)
    simpa only [mul_zero] using hh
  have hpartial (n : ℕ) : (∑ i ∈ Finset.range n,representationMap (a i))=x-r n := by
    induction n with
    | zero => simp [hr0]
    | succ n ih =>
      rw [Finset.sum_range_succ,ih,hrstep]
      abel
  have hsum : HasSum (fun n => representationMap (a n)) x := by
    apply (hasSum_iff_tendsto_nat_of_summable_norm hnorm).mpr
    simp_rw [hpartial]
    simpa only [sub_zero] using tendsto_const_nhds.sub hrtend
  let A : Segment → ℝ := fun S => ∑' n,(a n).val S
  have hAcost : representationCost A≤ ENNReal.ofReal (‖x‖+e/2) :=
    (representationCost_tsum (fun n => (a n).val) hcost).trans hcostbound
  have hA : representationCost A≠∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hAcost
  refine ⟨A,hA,?_,?_⟩
  · exact (representedCore_tsum (fun n => (a n).val) hcost hA).trans hsum.tsum_eq
  · have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hAcost
    rw [ENNReal.toReal_ofReal (by positivity : 0≤‖x‖+e/2)] at hh
    linarith

def coreCoordinates : DualCore →ₗ[ℝ] (Node → ℝ) where
  toFun x v := coordinateFunctional unitTests v x
  map_add' x y := by ext v; exact map_add _ _ _
  map_smul' c x := by ext v; exact map_smul _ _ _

lemma coreCoordinates_injective : Function.Injective coreCoordinates := by
  intro x y h
  apply sub_eq_zero.mp
  apply core_coordinates_total
  intro v
  rw [map_sub]
  exact sub_eq_zero.mpr (congrFun h v)

/-- The linear output of literal arrays, with absolute convergence proved for every finite-cost array. -/

def representationOutputMap : CostDomain →ₗ[ℝ] (Node → ℝ) := coreCoordinates.comp representationMap

lemma representationOutputMap_apply (a : CostDomain) :
    representationOutputMap a=representationOutput a.val := by
  ext v
  exact representedCore_coordinate a.val a.property v

/-- The segment-start space consists of coordinate fields represented by finite-cost countable signed segment arrays. Its norm equals the infimum over exactly these representations. -/

def StartSpace := ↥(LinearMap.range representationOutputMap)

instance : AddCommGroup StartSpace := inferInstanceAs (AddCommGroup ↥(LinearMap.range representationOutputMap))
instance : Module ℝ StartSpace := inferInstanceAs (Module ℝ ↥(LinearMap.range representationOutputMap))

lemma coreCoordinates_representable (x : DualCore) : coreCoordinates x ∈ LinearMap.range representationOutputMap := by
  obtain ⟨a,ha,hx,hc⟩ := exists_representation_near_norm x (by norm_num : (0:ℝ)<1)
  refine ⟨⟨a,ha⟩,?_⟩
  change coreCoordinates (representedCore a ha)=coreCoordinates x
  rw [hx]

def coreStartMap : DualCore →ₗ[ℝ] StartSpace where
  toFun x := ⟨coreCoordinates x,coreCoordinates_representable x⟩
  map_add' x y := Subtype.ext (map_add coreCoordinates x y)
  map_smul' c x := Subtype.ext (map_smul coreCoordinates c x)

lemma coreStartMap_bijective : Function.Bijective coreStartMap := by
  constructor
  · intro x y h
    exact coreCoordinates_injective (congrArg Subtype.val h)
  · intro x
    obtain ⟨a,ha⟩ := x.property
    exact ⟨representationMap a,Subtype.ext ha⟩

def coreStartEquiv : DualCore ≃ₗ[ℝ] StartSpace := LinearEquiv.ofBijective coreStartMap coreStartMap_bijective

def startCoreEquiv : StartSpace ≃ₗ[ℝ] DualCore := coreStartEquiv.symm

instance : Norm StartSpace := ⟨fun x => ‖startCoreEquiv x‖⟩

theorem startNormCore : NormedSpace.Core ℝ StartSpace where
  norm_nonneg x := norm_nonneg (startCoreEquiv x)
  norm_smul c x := by change ‖startCoreEquiv (c • x)‖=‖c‖*‖startCoreEquiv x‖; rw [map_smul,norm_smul]
  norm_triangle x y := by change ‖startCoreEquiv (x+y)‖≤_; rw [map_add]; exact norm_add_le _ _
  norm_eq_zero_iff x := by
    change ‖startCoreEquiv x‖=0 ↔ x=0
    rw [norm_eq_zero]
    exact map_eq_zero_iff _ startCoreEquiv.injective

instance : NormedAddCommGroup StartSpace := NormedAddCommGroup.ofCore startNormCore
instance : NormedSpace ℝ StartSpace := NormedSpace.ofCore startNormCore

def startCoreIsometry : StartSpace ≃ₗᵢ[ℝ] DualCore := { startCoreEquiv with norm_map' := fun _ => rfl }

instance : CompleteSpace StartSpace := startCoreIsometry.toIsometryEquiv.completeSpace

theorem start_reflexive : IsReflexive StartSpace := reflexive_equiv startCoreIsometry.toContinuousLinearEquiv core_reflexive

lemma startCore_coordinate (x : StartSpace) (v : Node) :
    coordinateFunctional unitTests v (startCoreEquiv x)=x.val v := by
  have h := coreStartEquiv.apply_symm_apply x
  exact congrFun (congrArg Subtype.val h) v

lemma representedCore_eq_startCore (x : StartSpace) (a : CostDomain)
    (ha : representationOutput a.val=x.val) : representedCore a.val a.property=startCoreEquiv x := by
  apply coreCoordinates_injective
  ext v
  change coordinateFunctional unitTests v (representedCore a.val a.property)=coordinateFunctional unitTests v (startCoreEquiv x)
  calc
    _ = representationOutput a.val v := representedCore_coordinate a.val a.property v
    _ = x.val v := congrFun ha v
    _ = _ := (startCore_coordinate x v).symm

/-- Exactly the original infimal forest representation formula, including all
finite-cost countable arrays and the original signed coordinate output. -/
def literalStartNorm (x : Node → ℝ) : ℝ :=
  sInf {c : ℝ | ∃ a : CostDomain,representationOutput a.val=x ∧ (representationCost a.val).toReal=c}

theorem start_norm_eq_infimum (x : StartSpace) : ‖x‖=literalStartNorm x.val := by
  let C : Set ℝ := {c | ∃ a : CostDomain,representationOutput a.val=x.val ∧ (representationCost a.val).toReal=c}
  have hbdd : BddBelow C := ⟨0,by rintro c ⟨a,ha,rfl⟩; exact ENNReal.toReal_nonneg⟩
  have hne : C.Nonempty := by
    obtain ⟨a,ha⟩ := x.property
    refine ⟨(representationCost a.val).toReal,a,?_,rfl⟩
    exact (representationOutputMap_apply a).symm.trans ha
  change ‖x‖=sInf C
  apply le_antisymm
  · apply le_csInf hne
    rintro c ⟨a,ha,rfl⟩
    change ‖startCoreEquiv x‖≤_
    rw [← representedCore_eq_startCore x a ha]
    exact representedCore_norm _ _
  · apply le_of_forall_pos_le_add
    intro e he
    obtain ⟨a,ha,hx,hc⟩ := exists_representation_near_norm (startCoreEquiv x) he
    have hout : representationOutput a=x.val := by
      ext v
      rw [← representedCore_coordinate a ha v,hx,startCore_coordinate]
    have hh : (representationCost a).toReal ∈ C := ⟨⟨a,ha⟩,hout,rfl⟩
    exact (csInf_le hbdd hh).trans hc.le

end BoundedTreePotentials.Segments

end

end OAI
