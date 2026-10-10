import OAI.Analysis.DiamondDistortion.InfimalCost

namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

open scoped ENNReal

namespace PathModel
open RecursiveModel
abbrev L1 (h : ℕ) := lp (fun _ : Coord h => ℝ) 1
abbrev L2 (h : ℕ) := lp (fun _ : Coord h => ℝ) 2

def branch (h : ℕ) (s : Coord h) : L2 h := ∑ r ∈ ancestors h s,lp.single 2 r (1:ℝ)
@[simp] lemma branch_apply (h : ℕ) (s r : Coord h) :
    branch h s r=if r ∈ ancestors h s then 1 else 0 := by
  change (lp.evalₗ (𝕜 := ℝ) (fun _ : Coord h => ℝ) 2 r) (branch h s)=_
  rw [branch,map_sum]
  simp only [lp.evalₗ_apply,lp.single_apply,Finset.sum_pi_single]
lemma ancestors_card (h : ℕ) (s : Coord h) : (ancestors h s).card ≤ h+1 := by
  induction h with
  | zero => simp [ancestors]
  | succ h ih =>
    cases s with
    | inl u => simp [ancestors]
    | inr a =>
      calc
        _ ≤ ((ancestors h a.2).image (fun t => Sum.inr (a.1,t))).card+1 := Finset.card_insert_le _ _
        _ ≤ (ancestors h a.2).card+1 := Nat.add_le_add_right (Finset.card_image_le) _
        _ ≤ _ := by have := ih a.2; omega
lemma branch_norm (h : ℕ) (s : Coord h) : ‖branch h s‖ ≤ (h+1:ℝ) := by
  calc
    _ ≤ ∑ r ∈ ancestors h s,‖(lp.single 2 r (1:ℝ) : L2 h)‖ := by
      unfold branch
      exact norm_sum_le (ancestors h s) (fun r => (lp.single 2 r (1:ℝ) : L2 h))
    _ = ((ancestors h s).card:ℝ) := by
      simp only [lp.norm_single (by norm_num : (0:ℝ≥0∞) < 2),norm_one,Finset.sum_const, nsmul_eq_mul,mul_one]
    _ ≤ _ := by exact_mod_cast ancestors_card h s

lemma summable_abs {h : ℕ} (μ : L1 h) : Summable (fun s => |μ s|) := by
  simpa only [ENNReal.toReal_one,Real.rpow_one,Real.norm_eq_abs] using (lp.memℓp μ).summable (by norm_num : 0 < (1:ℝ≥0∞).toReal)
lemma tsum_abs {h : ℕ} (μ : L1 h) : ∑' s,|μ s|=‖μ‖ := by
  simpa only [ENNReal.toReal_one,Real.rpow_one,Real.norm_eq_abs,one_div_one] using (lp.norm_eq_tsum_rpow (by norm_num : 0 < (1:ℝ≥0∞).toReal) μ).symm
lemma path_summable_norm {h : ℕ} (μ : L1 h) : Summable (fun s => ‖μ s • branch h s‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ ((summable_abs μ).mul_right (h+1:ℝ))
  intro s
  rw [norm_smul,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (branch_norm h s) (abs_nonneg _)
lemma path_summable {h : ℕ} (μ : L1 h) : Summable (fun s => μ s • branch h s) :=
  (path_summable_norm μ).of_norm

def path (h : ℕ) : L1 h →L[ℝ] L2 h :=
  LinearMap.mkContinuous {
    toFun μ := ∑' s,μ s • branch h s
    map_add' μ ν := by
      simp only [lp.coeFn_add,Pi.add_apply,add_smul]
      exact (path_summable μ).tsum_add (path_summable ν)
    map_smul' c μ := by
      simp only [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,mul_smul]
      exact (path_summable μ).tsum_const_smul c }
    (h+1:ℝ) (by
      intro μ
      calc
        _ ≤ ∑' s,‖μ s • branch h s‖ := norm_tsum_le_tsum_norm (path_summable_norm μ)
        _ ≤ ∑' s,|μ s| * (h+1:ℝ) := (path_summable_norm μ).tsum_le_tsum (fun s => by
          rw [norm_smul,Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left (branch_norm h s) (abs_nonneg _)) ((summable_abs μ).mul_right _)
        _ = _ := by rw [tsum_mul_right,tsum_abs]; ring)
lemma path_apply (h : ℕ) (μ : L1 h) (r : Coord h) :
    path h μ r=∑' s,if r ∈ ancestors h s then μ s else 0 := by
  change (lp.evalCLM ℝ (fun _ : Coord h => ℝ) 2 r) (∑' s,μ s • branch h s)=_
  rw [ContinuousLinearMap.map_tsum _ (path_summable μ)]
  simp only [map_smul,lp.evalCLM,LinearMap.mkContinuous_apply,lp.evalₗ_apply,branch_apply,smul_eq_mul,mul_ite,mul_one,mul_zero]
lemma path_coordinate (h : ℕ) (μ : L1 h) (r : Coord h) : |path h μ r| ≤ ‖μ‖ := by
  let ev := lp.evalCLM ℝ (fun _ : Coord h => ℝ) 2 r
  have hs : Summable (fun s => ev (μ s • branch h s)) := ev.summable (path_summable μ)
  have hsn : Summable (fun s => ‖ev (μ s • branch h s)‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ (summable_abs μ)
    intro s
    change |μ s * branch h s r| ≤ |μ s|
    rw [branch_apply]
    split_ifs <;> simp
  have he : |path h μ r|=‖∑' s,ev (μ s • branch h s)‖ := by
    rw [← ContinuousLinearMap.map_tsum ev (path_summable μ)]
    rfl
  rw [he]
  calc
    _ ≤ ∑' s,‖ev (μ s • branch h s)‖ := norm_tsum_le_tsum_norm hsn
    _ ≤ ∑' s,|μ s| := hsn.tsum_le_tsum (fun s => by
      change |μ s * branch h s r| ≤ |μ s|
      rw [branch_apply]; split_ifs <;> simp) (summable_abs μ)
    _ = _ := tsum_abs μ

/-- The admissible decompositions use full ℓ² and ℓ¹, and the norm on their
    pair is exactly the linear (q=1) or quadratic (q=2) representation cost. -/
def presentation (q : ℝ≥0∞) [Fact (1 ≤ q)] (h : ℕ) :
    InfimalCost.Presentation (WithLp q (L2 h × L1 h)) (L2 h) where
  output := {
    toFun d := d.fst+path h d.snd
    map_add' d e := by simp only [WithLp.add_fst,WithLp.add_snd,map_add]; abel
    map_smul' c d := by simp only [WithLp.smul_fst,WithLp.smul_snd,map_smul,smul_add,RingHom.id_apply] }
  sectionMap := {
    toFun v := WithLp.toLp q (v,0)
    map_add' v w := by
      apply WithLp.ofLp_injective q
      simp only [WithLp.ofLp_add,Prod.mk_add_mk,add_zero]
    map_smul' c v := by
      apply WithLp.ofLp_injective q
      simp only [WithLp.ofLp_smul,RingHom.id_apply,Prod.smul_mk,smul_zero] }
  right_inverse v := by simp
@[simp] lemma presentation_output (q : ℝ≥0∞) [Fact (1 ≤ q)] (h : ℕ)
    (d : WithLp q (L2 h × L1 h)) : (presentation q h).output d=d.fst+path h d.snd := rfl
@[simp] lemma presentation_section (q : ℝ≥0∞) [Fact (1 ≤ q)] (h : ℕ) (v : L2 h) :
    (presentation q h).sectionMap v=WithLp.toLp q (v,0) := rfl

/-- Literal infimum over all decompositions z=h+Jμ. -/
def cost (q : ℝ≥0∞) [Fact (1 ≤ q)] (h : ℕ) : Seminorm ℝ (L2 h) := (presentation q h).seminorm
lemma linear_cost_formula (h : ℕ) (v : L2 h) :
    cost 1 h v=sInf {r : ℝ | ∃ w : L2 h,∃ μ : L1 h,w+path h μ=v ∧ ‖w‖+‖μ‖=r} := by
  rw [cost,(presentation 1 h).eq_sInf]
  congr 1
  ext r
  constructor
  · rintro ⟨d,hd,hr⟩
    exact ⟨d.fst,d.snd,hd,(WithLp.prod_norm_eq_of_L1 d).symm.trans hr⟩
  · rintro ⟨w,μ,hd,hr⟩
    exact ⟨WithLp.toLp 1 (w,μ),hd,(WithLp.prod_norm_eq_of_L1 _).trans hr⟩
lemma quadratic_cost_formula (h : ℕ) (v : L2 h) :
    cost 2 h v=sInf {r : ℝ | ∃ w : L2 h,∃ μ : L1 h,w+path h μ=v ∧ Real.sqrt (‖w‖^2+‖μ‖^2)=r} := by
  rw [cost,(presentation 2 h).eq_sInf]
  congr 1
  ext r
  constructor
  · rintro ⟨d,hd,hr⟩
    exact ⟨d.fst,d.snd,hd,(WithLp.prod_norm_eq_of_L2 d).symm.trans hr⟩
  · rintro ⟨w,μ,hd,hr⟩
    exact ⟨WithLp.toLp 2 (w,μ),hd,(WithLp.prod_norm_eq_of_L2 _).trans hr⟩

lemma representation_coordinate (q : ℝ≥0∞) [Fact (1 ≤ q)] (h : ℕ)
    (d : WithLp q (L2 h × L1 h)) (r : Coord h) :
    |(presentation q h).output d r| ≤ ‖d.fst‖+‖d.snd‖ := by
  change |d.fst r+path h d.snd r| ≤ _
  exact (abs_add_le _ _).trans (add_le_add
    (by simpa only [Real.norm_eq_abs] using lp.norm_apply_le_norm (by norm_num : (2:ℝ≥0∞) ≠ 0) d.fst r)
    (path_coordinate h d.snd r))
lemma linear_coordinate (h : ℕ) (v : L2 h) (r : Coord h) : |v r| ≤ cost 1 h v := by
  have hh := (presentation 1 h).bound v (by norm_num : (0:ℝ) ≤ 1) (b := |v r|) (by
    intro d hd
    rw [← hd,one_mul,WithLp.prod_norm_eq_of_L1]
    exact representation_coordinate 1 h d r)
  simpa only [one_mul,cost] using hh
lemma quadratic_coordinate (h : ℕ) (v : L2 h) (r : Coord h) : |v r| ≤ Real.sqrt 2*cost 2 h v := by
  apply (presentation 2 h).bound v (Real.sqrt_nonneg 2)
  intro d hd
  rw [← hd]
  apply (representation_coordinate 2 h d r).trans
  have hs := WithLp.prod_norm_sq_eq_of_L2 d
  have hs2 : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hnn : 0 ≤ Real.sqrt 2*‖d‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hsq : (‖d.fst‖+‖d.snd‖)^2 ≤ (Real.sqrt 2*‖d‖)^2 := by
    rw [mul_pow,hs2,hs]
    nlinarith [sq_nonneg (‖d.fst‖-‖d.snd‖)]
  exact (sq_le_sq₀ (by positivity) hnn).mp hsq

lemma linear_le_norm (h : ℕ) (v : L2 h) : cost 1 h v ≤ ‖v‖ := by
  have hh := (presentation 1 h).le_representation ((presentation 1 h).right_inverse v)
  simpa only [cost,presentation_section,WithLp.prod_norm_eq_of_L1,WithLp.fst,WithLp.snd,WithLp.ofLp_toLp,norm_zero,add_zero] using hh
lemma quadratic_le_norm (h : ℕ) (v : L2 h) : cost 2 h v ≤ ‖v‖ := by
  have hh := (presentation 2 h).le_representation ((presentation 2 h).right_inverse v)
  simpa only [cost,presentation_section,WithLp.prod_norm_eq_of_L2,WithLp.fst,WithLp.snd,WithLp.ofLp_toLp,norm_zero,zero_pow (by decide : 2 ≠ 0),add_zero,Real.sqrt_sq_eq_abs,abs_norm] using hh

/-- Coordinate finite vectors inherit the same exact full-representation infimum. -/
def finiteEmbedding (h : ℕ) : Vec h →ₗ[ℝ] L2 h where
  toFun := finiteLp 2
  map_add' := finiteLp_add 2
  map_smul' c v := finiteLp_smul 2 c v
def finiteCost (q : ℝ≥0∞) [Fact (1 ≤ q)] (h : ℕ) : Seminorm ℝ (Vec h) :=
  (cost q h).comp (finiteEmbedding h)

end PathModel

namespace RecursiveModel
open scoped ENNReal
/-- The literal outer ℓ² norm of a family of finite component seminorms. -/
def outerValues (s : ∀ h,Seminorm ℝ (Vec (h+1))) (v : ForestVec) : ℕ →₀ ℝ :=
  componentValues (fun h => ⟨s h,map_zero (s h)⟩) v
@[simp] lemma outerValues_apply (s : ∀ h,Seminorm ℝ (Vec (h+1))) (v : ForestVec) (h : ℕ) :
    outerValues s v h=s h (components v h) := rfl
@[simp] lemma outerValues_zero (s : ∀ h,Seminorm ℝ (Vec (h+1))) : outerValues s 0=0 := componentValues_zero _
lemma outerValues_nonneg (s : ∀ h,Seminorm ℝ (Vec (h+1))) (v : ForestVec) (h : ℕ) :
    0 ≤ outerValues s v h := apply_nonneg (s h) _
lemma outerValues_add (s : ∀ h,Seminorm ℝ (Vec (h+1))) (v w : ForestVec) (h : ℕ) :
    outerValues s (v+w) h ≤ (outerValues s v+outerValues s w) h := by
  simp only [outerValues_apply,map_add,DFinsupp.add_apply,Finsupp.add_apply]
  exact map_add_le_add (s h) _ _
lemma outerValues_neg (s : ∀ h,Seminorm ℝ (Vec (h+1))) (v : ForestVec) :
    outerValues s (-v)=outerValues s v := by
  ext h
  simp only [outerValues_apply,map_neg,DFinsupp.neg_apply,map_neg_eq_map]
lemma outerValues_smul (s : ∀ h,Seminorm ℝ (Vec (h+1))) (t : ℝ) (v : ForestVec) :
    outerValues s (t • v)=|t| • outerValues s v := by
  ext h
  simp only [outerValues_apply,map_smul,DFinsupp.smul_apply,Finsupp.smul_apply,smul_eq_mul,map_smul_eq_mul,Real.norm_eq_abs]

def outerSeminorm (s : ∀ h,Seminorm ℝ (Vec (h+1))) : Seminorm ℝ ForestVec where
  toFun v := aggregate 2 (outerValues s v)
  map_zero' := by simp
  add_le' v w :=
    (aggregate_mono 2 _ _ (outerValues_nonneg s _) (outerValues_add s _ _)).trans (aggregate_add 2 _ _)
  neg' v := by rw [outerValues_neg]
  smul' t v := by rw [outerValues_smul,aggregate_smul,abs_abs,Real.norm_eq_abs]
lemma component_le_outer (s : ∀ h,Seminorm ℝ (Vec (h+1))) (v : ForestVec) (h : ℕ) :
    s h (components v h) ≤ outerSeminorm s v := by
  exact (le_abs_self _).trans (coordinate_le_aggregate 2 (outerValues s v) h)
end RecursiveModel

namespace PathModel

section
open RecursiveModel

def linearForestSeminorm : Seminorm ℝ ForestVec := outerSeminorm (fun h => finiteCost 1 (h+1))
def quadraticForestSeminorm : Seminorm ℝ ForestVec := outerSeminorm (fun h => finiteCost 2 (h+1))
lemma linear_forest_coordinate (v : ForestVec) (i : ForestCoord) : |v i| ≤ linearForestSeminorm v := by
  exact (linear_coordinate (i.1+1) (finiteEmbedding _ (components v i.1)) i.2).trans
    (component_le_outer (fun h => finiteCost 1 (h+1)) v i.1)
lemma quadratic_forest_coordinate (v : ForestVec) (i : ForestCoord) :
    |v i| ≤ Real.sqrt 2*quadraticForestSeminorm v := by
  exact (quadratic_coordinate (i.1+1) (finiteEmbedding _ (components v i.1)) i.2).trans
    (mul_le_mul_of_nonneg_left (component_le_outer (fun h => finiteCost 2 (h+1)) v i.1) (Real.sqrt_nonneg _))

/-- Original component root; this is distinct from a forest component index. -/
def root : (h : ℕ) → Coord h
  | 0 => ()
  | _+1 => Sum.inl ()
lemma root_ancestors (h : ℕ) : ancestors h (root h)={root h} := by cases h <;> rfl
lemma branch_root (h : ℕ) : branch h (root h)=lp.single 2 (root h) (1:ℝ) := by
  simp only [branch,root_ancestors,Finset.sum_singleton]
lemma path_single (h : ℕ) [DecidableEq (Coord h)] (s : Coord h) (c : ℝ) :
    path h (lp.single 1 s c)=c • branch h s := by
  change ∑' t,((lp.single 1 s c : L1 h) t) • branch h t = _
  rw [tsum_eq_single s]
  · rw [lp.single_apply_self]
  · intro t ht
    rw [lp.single_apply_ne (E := fun _ : Coord h => ℝ) 1 s c ht,zero_smul]
@[simp] lemma linear_root (h : ℕ) : cost 1 h (lp.single 2 (root h) (1:ℝ))=1 := by
  apply le_antisymm
  · exact (linear_le_norm h _).trans_eq (by rw [lp.norm_single (by norm_num : (0:ℝ≥0∞)<2),norm_one])
  · have hh := linear_coordinate h (lp.single 2 (root h) (1:ℝ)) (root h)
    simpa only [lp.single_apply_self,abs_one] using hh
@[simp] lemma quadratic_root (h : ℕ) : cost 2 h (lp.single 2 (root h) (1:ℝ))=1/Real.sqrt 2 := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  let e : L2 h := lp.single 2 (root h) 1
  let μ : L1 h := lp.single 1 (root h) 1
  have he : path h μ=e := by rw [path_single,one_smul,branch_root]
  let d := WithLp.toLp 2 ((1/2:ℝ) • e,(1/2:ℝ) • μ)
  have hd : (presentation 2 h).output d=e := by
    change (1/2:ℝ) • e+path h ((1/2:ℝ) • μ)=e
    rw [map_smul,he]
    module
  apply le_antisymm
  · have hb := (presentation 2 h).le_representation hd
    have hnorm : ‖d‖=1/Real.sqrt 2 := by
      dsimp [d]
      rw [WithLp.prod_norm_eq_of_L2]
      change Real.sqrt (‖(1/2:ℝ) • e‖^2+‖(1/2:ℝ) • μ‖^2)=_
      simp only [norm_smul,Real.norm_eq_abs,e,μ,lp.norm_single (by norm_num : (0:ℝ≥0∞)<2),lp.norm_single (by norm_num : (0:ℝ≥0∞)<1),norm_one,mul_one]
      norm_num
    exact hb.trans_eq hnorm
  · have hh := quadratic_coordinate h e (root h)
    simp only [e,lp.single_apply_self,abs_one] at hh
    exact (div_le_iff₀ hs).mpr (by simpa only [mul_comm] using hh)
end

open RecursiveModel PathApplications
/-- Exact path-cost completions on the original finite-height components. -/
def linearData : CoordinateCompletion.Data ForestCoord where
  seminorm := linearForestSeminorm
  coordinate_bound i := ⟨1,fun v => by simpa only [one_mul] using linear_forest_coordinate v i⟩
def quadraticData : CoordinateCompletion.Data ForestCoord where
  seminorm := quadraticForestSeminorm
  coordinate_bound i := ⟨Real.sqrt 2,fun v => quadratic_forest_coordinate v i⟩
abbrev LinearSpace := linearData.Space
abbrev QuadraticSpace := quadraticData.Space
def linearHeads : Midpoint.Heads ForestHead LinearSpace :=
  linearData.heads Subtype.val (fun S => ⟨forestHead S,forestHead_contains S⟩)
def quadraticHeads : Midpoint.Heads ForestHead QuadraticSpace :=
  quadraticData.heads Subtype.val (fun S => ⟨forestHead S,forestHead_contains S⟩)
lemma linearHeads_commutes : linearHeads.Commutes := linearData.heads_commutes _ _
lemma quadraticHeads_commutes : quadraticHeads.Commutes := quadraticData.heads_commutes _ _

/-- Positive flow and trimming are retained as independent exact intrinsic inputs. -/
theorem linear_flow_graph (hinput : FlowInput linearHeads (linearC^2))
    {D s : ℝ} (k : ℕ) (f : Diamond.Vertex k → LinearSpace) (hf : Diamond.HasDistortion k f D s) :
    1+(k:ℝ)/(2*linearC^2) ≤ D^2 ∧ (k:ℝ) ≤ 2*linearC^2*D^2 :=
  linear_flow linearHeads hinput k f hf
theorem linear_trimming_graph (hinput : FlowInput linearHeads 242)
    {D s : ℝ} (k : ℕ) (f : Diamond.Vertex k → LinearSpace) (hf : Diamond.HasDistortion k f D s) :
    1+(k:ℝ)/484 ≤ D^2 := linear_trimming linearHeads hinput k f hf
theorem linear_clipping_graph (hinput : linearHeads.ParametricInput (1/2) 4)
    {D s : ℝ} (k : ℕ) (f : Diamond.Vertex k → LinearSpace) (hf : Diamond.HasDistortion k f D s) :
    1+(k:ℝ)*clippingGamma D/(2*clippingQ D) ≤ D :=
  linear_clipping linearHeads hinput k f hf
theorem linear_vanishing_graph (hinput : linearHeads.TailVanishing) :
    ¬ Diamond.UniformEmbeddings LinearSpace := linearHeads.vanishing_obstruction hinput
theorem linear_vanishing_weak (hinput : linearHeads.TailVanishing) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : ℝ,0 ≤ ρ ∧ ρ < 1 ∧
    ∀ (x : LinearSpace) (z : ℕ → LinearSpace),Midpoint.WeaklyNull z → (∀ i,ε ≤ ‖z i‖) →
      (∀ i,‖x+z i‖ ≤ 1) → (∀ i,‖x-z i‖ ≤ 1) → ‖x‖ ≤ ρ :=
  linearHeads.vanishing_weak hinput hε

theorem quadratic_graph (hinput : ArbitraryTailInput quadraticHeads 8)
    {D s : ℝ} (k : ℕ) (f : Diamond.Vertex k → QuadraticSpace) (hf : Diamond.HasDistortion k f D s) :
    1+(k:ℝ)/64 ≤ D^2 := quadratic_cost quadraticHeads hinput k f hf
theorem stopped_graph (hinput : StoppedInput quadraticHeads)
    {D s : ℝ} (k : ℕ) (f : Diamond.Vertex k → QuadraticSpace) (hf : Diamond.HasDistortion k f D s) :
    (k:ℝ) ≤ 144*D^2 := stopped_flow quadraticHeads hinput k f hf
theorem quadratic_component_graph (hinput : ComponentSumInput QuadraticSpace)
    {D s e : ℝ} (he : 0 < e) (he16 : e ≤ 1/16) (hsmall : 17*(2*e)^((1:ℝ)/6) < 1/(2*D))
    (k : ℕ) (f : Diamond.Vertex k → QuadraticSpace) (hf : Diamond.HasDistortion k f D s) :
    (1+e/2)^k ≤ D := component_sum hinput he he16 hsmall k f hf
end PathModel

end DiamondDistortion

end

end OAI
