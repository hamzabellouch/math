import OAI.Analysis.DiamondDistortion.Relations

namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

open scoped ENNReal

namespace StartModel

section
open RecursiveModel PathModel
/-- A local bundle used only to recurse over the finite tree height. -/
structure RealNormed where
  carrier : Type
  [group : NormedAddCommGroup carrier]
  [space : NormedSpace ℝ carrier]
attribute [instance] RealNormed.group RealNormed.space
instance : CoeSort RealNormed Type := ⟨RealNormed.carrier⟩

/-- At each node the root-start coefficients form ℓ¹ over the possible endpoints;
    the children form ℓ² of their own representation spaces. The outer ℓ¹ pair
    is exactly q_s=m_s+(Σ q_c²)^(1/2). -/
abbrev representationModel : ℕ → RealNormed
  | 0 => ⟨ℝ⟩
  | h+1 =>
      let M := representationModel h
      ⟨WithLp 1 (L1 (h+1) × lp (fun _ : ℕ => M) 2)⟩
abbrev Rep (h : ℕ) := representationModel h

/-- Coordinate output, including the absolutely summable root-start paths and
    the child contribution. No finite-support restriction is made on a Rep. -/
def output : (h : ℕ) → (Rep h →ₗ[ℝ] (Coord h → ℝ))
  | 0 => {
      toFun a := fun _ => a
      map_add' a b := rfl
      map_smul' c a := rfl }
  | h+1 => {
      toFun d := fun r => match r with
        | .inl _ => path (h+1) d.fst (root (h+1))
        | .inr (i,s) => path (h+1) d.fst (.inr (i,s))+output h (d.snd i) s
      map_add' d e := by
        funext r
        cases r with
        | inl u => simp only [WithLp.add_fst,map_add,lp.coeFn_add,Pi.add_apply]
        | inr a => simp only [WithLp.add_fst,WithLp.add_snd,map_add,lp.coeFn_add,Pi.add_apply]; ring
      map_smul' c d := by
        funext r
        cases r with
        | inl u => simp only [WithLp.smul_fst,map_smul,lp.coeFn_smul,Pi.smul_apply,RingHom.id_apply]
        | inr a => simp only [WithLp.smul_fst,WithLp.smul_snd,map_smul,lp.coeFn_smul,Pi.smul_apply,RingHom.id_apply,smul_eq_mul]; ring }

lemma output_coordinate (h : ℕ) (d : Rep h) (r : Coord h) : |output h d r| ≤ ‖d‖ := by
  induction h with
  | zero => exact le_rfl
  | succ h ih =>
    change |output (h+1) d r| ≤ ‖(d : WithLp 1 (L1 (h+1) × lp (fun _ : ℕ => Rep h) 2))‖
    rw [WithLp.prod_norm_eq_of_L1]
    cases r with
    | inl u =>
      exact (path_coordinate (h+1) d.fst (root (h+1))).trans (le_add_of_nonneg_right (norm_nonneg _))
    | inr a =>
      change |path (h+1) d.fst (.inr a)+output h (d.snd a.1) a.2| ≤ _
      exact (abs_add_le _ _).trans (add_le_add (path_coordinate (h+1) d.fst (.inr a))
        ((ih (d.snd a.1) a.2).trans (lp.norm_apply_le_norm (by norm_num : (2:ℝ≥0∞) ≠ 0) d.snd a.1)))

/-- Singleton segments, used only as a right inverse, not as a restriction on
    the allowed representations. -/
abbrev atom : (h : ℕ) → Coord h → (ℝ →ₗ[ℝ] Rep h)
  | 0,_ => LinearMap.id
  | h+1,.inl _ =>
    (WithLp.linearEquiv 1 ℝ (L1 (h+1) × lp (fun _ : ℕ => Rep h) 2)).symm.toLinearMap.comp
      ((lp.lsingle (𝕜 := ℝ) (E := fun _ : Coord (h+1) => ℝ) 1 (root (h+1))).prod 0)
  | h+1,.inr (i,s) =>
    (WithLp.linearEquiv 1 ℝ (L1 (h+1) × lp (fun _ : ℕ => Rep h) 2)).symm.toLinearMap.comp
      ((0 : ℝ →ₗ[ℝ] L1 (h+1)).prod ((lp.lsingle (𝕜 := ℝ) (E := fun _ : ℕ => Rep h) 2 i).comp (atom h s)))

lemma output_atom (h : ℕ) (s r : Coord h) (c : ℝ) :
    output h (atom h s c) r=if s=r then c else 0 := by
  induction h with
  | zero => simp [output,atom]
  | succ h ih =>
    cases s with
    | inl u =>
      cases u
      cases r with
      | inl v =>
        cases v
        rw [ite_eq_left rfl]
        change (lp.evalₗ (𝕜 := ℝ) (fun _ : Coord (h+1) => ℝ) 2 (root (h+1)))
          (path (h+1) (lp.single 1 (root (h+1)) c))=c
        rw [path_single (h+1) (root (h+1)) c,branch_root (h+1)]
        simp only [map_smul,lp.evalₗ_apply,lp.single_apply_self,smul_eq_mul,mul_one]
      | inr a =>
        simp only [reduceCtorEq,ite_false]
        change (lp.evalₗ (𝕜 := ℝ) (fun _ : Coord (h+1) => ℝ) 2 (.inr a))
          (path (h+1) (lp.single 1 (root (h+1)) c))+output h 0 a.2=0
        rw [path_single (h+1) (root (h+1)) c,branch_root (h+1),map_zero]
        simp only [map_smul,lp.evalₗ_apply,lp.single_apply,root,
          smul_eq_mul,Pi.zero_apply,add_zero]
        simp
    | inr b =>
      cases r with
      | inl v =>
        simp only [reduceCtorEq,ite_false]
        change path (h+1) 0 (root (h+1))=0
        rw [map_zero]
        rfl
      | inr a =>
        change path (h+1) 0 (.inr a)+output h ((lp.single 2 b.1 (atom h b.2 c) :
          lp (fun _ : ℕ => Rep h) 2) a.1) a.2=_
        simp only [map_zero,lp.coeFn_zero,Pi.zero_apply,zero_add]
        by_cases he : a.1=b.1
        · rw [he,lp.single_apply_self,ih]
          simp [he,Prod.ext_iff]
        · rw [lp.single_apply_ne (E := fun _ : ℕ => Rep h) 2 b.1 (atom h b.2 c) he]
          simp [map_zero,Prod.ext_iff,Ne.symm he]

/-- The infimum over the full nested ℓ¹/ℓ² representation space. -/
def finiteSection (h : ℕ) : Vec h →ₗ[ℝ] Rep h := Finsupp.lsum ℝ (atom h)

def relation (h : ℕ) : InfimalCost.Relation (Rep h) (Vec h) (Coord h → ℝ) where
  output := output h
  value := {
    toFun v := fun s => v s
    map_add' a b := rfl
    map_smul' c a := rfl }
  sectionMap := finiteSection h
  section_output v := by
    ext r
    change output h (v.sum fun s a => atom h s a) r=v r
    rw [Finsupp.sum, map_sum]
    simp only [Finset.sum_apply,output_atom]
    rw [Finset.sum_ite_eq']
    split_ifs with hr
    · rfl
    · exact (Finsupp.notMem_support_iff.mp hr).symm

def finiteCost (h : ℕ) : Seminorm ℝ (Vec h) := (relation h).seminorm
lemma finiteCost_eq_sInf (h : ℕ) (v : Vec h) :
    finiteCost h v=sInf {r : ℝ | ∃ d : Rep h,output h d=(fun s => v s) ∧ ‖d‖=r} :=
  (relation h).eq_sInf v
lemma coordinate_le_cost (h : ℕ) (v : Vec h) (r : Coord h) : |v r| ≤ finiteCost h v := by
  apply (relation h).bound v
  intro d hd
  have he : output h d r=v r := congrFun hd r
  rw [← he]
  exact output_coordinate h d r

def forestSeminorm : Seminorm ℝ ForestVec := outerSeminorm (fun h => finiteCost (h+1))
lemma forest_coordinate (v : ForestVec) (i : ForestCoord) : |v i| ≤ forestSeminorm v := by
  exact (coordinate_le_cost (i.1+1) (components v i.1) i.2).trans
    (component_le_outer (fun h => finiteCost (h+1)) v i.1)

end

open RecursiveModel PathApplications

def data : CoordinateCompletion.Data ForestCoord where
  seminorm := forestSeminorm
  coordinate_bound i := ⟨1,fun p => by simpa only [one_mul] using forest_coordinate p i⟩
abbrev Space := data.Space
def heads : Midpoint.Heads ForestHead Space :=
  data.heads Subtype.val (fun S => ⟨forestHead S,forestHead_contains S⟩)

theorem graph (hinput : StartInput heads) {D s : ℝ}
    (k : ℕ) (f : Diamond.Vertex k → Space) (hf : Diamond.HasDistortion k f D s) :
    1+(k:ℝ)/128 ≤ D^2 := start_cost heads hinput k f hf

lemma representation_norm_zero (d : Rep 0) : ‖d‖=|d| := rfl
lemma representation_norm_succ (h : ℕ) (d : Rep (h+1)) :
    ‖d‖=‖d.fst‖+‖d.snd‖ := WithLp.prod_norm_eq_of_L1 d
lemma root_start_mass (h : ℕ) (d : Rep (h+1)) :
    ‖d.fst‖=∑' s : Coord (h+1),|d.fst s| := (PathModel.tsum_abs d.fst).symm
lemma children_cost_sq (h : ℕ) (d : Rep (h+1)) :
    ‖d.snd‖^2=∑' i : ℕ,‖d.snd i‖^2 := by
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
    lp.norm_rpow_eq_tsum (p := 2) (by norm_num) d.snd

end StartModel

namespace PathModel
open PathApplications

theorem quadratic_relative_graph (hinput : RelativeInput quadraticHeads) {D s : ℝ}
    (k : ℕ) (f : Diamond.Vertex k → QuadraticSpace) (hf : Diamond.HasDistortion k f D s) :
    (1+relativeDelta D)^k ≤ D := relative_cost quadraticHeads hinput k f hf

theorem quadratic_tail_seven_graph (hinput : ArbitraryTailInput quadraticHeads 7) {D s : ℝ}
    (k : ℕ) (f : Diamond.Vertex k → QuadraticSpace) (hf : Diamond.HasDistortion k f D s) :
    D⁻¹ ≤ (1-D⁻¹^2/2000)^k := tail_seven quadraticHeads hinput k f hf

theorem quadratic_pruning_graph (hinput : ArbitraryTailInput quadraticHeads 9) {D s γ : ℝ}
    (hγ : 0 < γ) (hγhalf : γ < 1/2)
    (hsmall : 9*Real.sqrt ((1+γ)^2-(1-2*γ)^2) < 2*D⁻¹/3)
    (k : ℕ) (f : Diamond.Vertex k → QuadraticSpace) (hf : Diamond.HasDistortion k f D s) :
    D⁻¹ ≤ (1-γ)^k := tail_pruning quadraticHeads hinput hγ hγhalf hsmall k f hf
end PathModel

end DiamondDistortion

end

end OAI
