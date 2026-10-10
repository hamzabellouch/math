import OAI.Geometry.UnitDistances.Circles

namespace OAI

namespace PlanarUnitDistances.OrganizedProfiles
open Finset PlaceLevels WeightedAbsoluteValues ActualProfiles ProfileBudget PlaceLogGeometry
open scoped Classical BigOperators
noncomputable section
variable {K : Type*} {V P Q H : Type} [Field K] [NumberField K]
  [Fintype V] [Fintype P] [Fintype Q]
variable (G : Input K V P Q H)

def jump (p : P) (q : Q) : K := G.z (G.point p)-G.z (G.center q)
def ratio (a : Q×(P×P)) : K := jump G a.2.1 a.1/jump G a.2.2 a.1

theorem log_ratio (a : Q×(P×P)) (v : Place K G.support)
    (h₁ : jump G a.2.1 a.1≠0) (h₂ : jump G a.2.2 a.1≠0) :
    Real.log (av K v (ratio G a))= -(G.threshold v a.2.1 a.1-G.threshold v a.2.2 a.1) := by
  rw [ratio,PlaceLogGeometry.log_div _ h₁ h₂]
  unfold Input.threshold jump
  ring

lemma ratio_supported (a : Q×(P×P))
    (h₁ : jump G a.2.1 a.1≠0) (h₂ : jump G a.2.2 a.1≠0)
    (hs₁ : jump G a.2.1 a.1∈G.support) (hs₂ : jump G a.2.2 a.1∈G.support) :
    supported G.support (ratio G a) :=
  supported_div h₁ h₂ (supported_of_mem hs₁) (supported_of_mem hs₂)

lemma log_residual (a : Q×(P×P))
    (h₁ : jump G a.2.1 a.1≠0) (h₂ : jump G a.2.2 a.1≠0)
    (hs₁ : jump G a.2.1 a.1∈G.support) (hs₂ : jump G a.2.2 a.1∈G.support) :
    l1 G (fun v => Real.log (av K v (ratio G a))+G.profile a.2.1 v-G.profile a.2.2 v)≤error G true a := by
  have he : l1 G (fun v => Real.log (av K v (ratio G a))+G.profile a.2.1 v-G.profile a.2.2 v)=
      l1 G (fun v => G.threshold v a.2.1 a.1-G.threshold v a.2.2 a.1-(G.profile a.2.1 v-G.profile a.2.2 v)) := by
    unfold l1 weighted
    congr 1
    apply sum_congr rfl
    intro v _
    dsimp only
    rw [log_ratio G a v h₁ h₂]
    convert abs_neg (G.threshold v a.2.1 a.1-G.threshold v a.2.2 a.1-(G.profile a.2.1 v-G.profile a.2.2 v)) using 1; congr 1; ring
  rw [he]
  exact ProfileBudget.residual G a hs₁ hs₂

lemma height_lower [IsGalois ℚ K] (a : Q×(P×P))
    (h₁ : jump G a.2.1 a.1≠0) (h₂ : jump G a.2.2 a.1≠0)
    (hs₁ : jump G a.2.1 a.1∈G.support) (hs₂ : jump G a.2.2 a.1∈G.support) :
    height G a.2.1+height G a.2.2-error G false a≤2*exactHeight K (ratio G a) := by
  rw [←height_identity G.support (show ratio G a≠0 from div_ne_zero h₁ h₂) (ratio_supported G a h₁ h₂ hs₁ hs₂)]
  have he : (LevelScale.weight K:ℝ)*(∑v : Place K G.support,|Real.log (av K v (ratio G a))|)=
      l1 G (fun v => G.threshold v a.2.1 a.1-G.threshold v a.2.2 a.1) := by
    unfold l1 weighted
    congr 1
    apply sum_congr rfl
    intro v _
    dsimp only
    rw [log_ratio G a v h₁ h₂,abs_neg]
  rw [he]
  exact ProfileBudget.size G a hs₁ hs₂

theorem selected [IsGalois ℚ K] (a : Q×(P×P)) {J δ : ℝ}
    (hJ : 0<J) (hδ : 0≤δ) (hδ' : δ≤1/3)
    (h₁ : jump G a.2.1 a.1≠0) (h₂ : jump G a.2.2 a.1≠0)
    (hs₁ : jump G a.2.1 a.1∈G.support) (hs₂ : jump G a.2.2 a.1∈G.support)
    (hband : J≤height G a.2.1+height G a.2.2 ∧ height G a.2.1+height G a.2.2≤2*J)
    (herr : error G true a+error G false a≤δ*(height G a.2.1+height G a.2.2)) :
    a.2.1≠a.2.2 ∧ J/3≤exactHeight K (ratio G a) ∧
      l1 G (fun v => Real.log (av K v (ratio G a))+G.profile a.2.1 v-G.profile a.2.2 v)≤2*δ*J := by
  have e₁ := error_nonneg G true a
  have e₂ := error_nonneg G false a
  have hlow := height_lower G a h₁ h₂ hs₁ hs₂
  have hw := add_nonneg (height_nonneg G a.2.1) (height_nonneg G a.2.2)
  have hh : J/3≤exactHeight K (ratio G a) := by
    nlinarith [mul_le_mul_of_nonneg_right hδ' hw]
  refine ⟨?_,hh,?_⟩
  · intro he
    have hz : ratio G a=1 := by unfold ratio; rw [he,div_self h₂]
    rw [hz,exactHeight_one] at hh
    linarith
  · have hr := log_residual G a h₁ h₂ hs₁ hs₂
    nlinarith [mul_le_mul_of_nonneg_left hband.2 hδ]

theorem identity (a : Q×(P×P))
    (h₁ : jump G a.2.1 a.1*(G.w (G.point a.2.1)-G.w (G.center a.1))=1)
    (h₂ : jump G a.2.2 a.1*(G.w (G.point a.2.2)-G.w (G.center a.1))=1) :
    (G.z (G.point a.2.1)-G.z (G.point a.2.2))*(G.w (G.point a.2.1)-G.w (G.point a.2.2))=
      2-ratio G a-(ratio G a)⁻¹ := by
  have hn₁ : jump G a.2.1 a.1≠0 := by intro hz; simp [hz] at h₁
  have hn₂ : jump G a.2.2 a.1≠0 := by intro hz; simp [hz] at h₂
  calc
    _ = (jump G a.2.1 a.1-jump G a.2.2 a.1)*
        ((G.w (G.point a.2.1)-G.w (G.center a.1))-(G.w (G.point a.2.2)-G.w (G.center a.1))) := by
      unfold jump
      ring
    _ = _ := PlaceLogGeometry.unit_pair_identity hn₁ hn₂ h₁ h₂
end
end PlanarUnitDistances.OrganizedProfiles

namespace PlanarUnitDistances.OrganizedGraph
open Finset PlaceLevels WeightedAbsoluteValues ActualProfiles ProfileBudget PlaceLogGeometry OrganizedProfiles
open scoped Classical BigOperators
noncomputable section
variable {K : Type*} {V P Q H : Type} [Field K] [NumberField K] [IsGalois ℚ K]
  [Fintype V] [Fintype P] [Fintype Q]
variable (G : Input K V P Q H) (A : Q×(P×P) → Prop)

def edge (p r : P) : Prop := ∃q,A (q,(p,r))
def label (p r : P) : K := if h : edge A p r then ratio G (h.choose,(p,r)) else 1

omit [IsGalois ℚ K] in
lemma label_eq {p r : P} (h : edge A p r) :
    label G A p r=ratio G (h.choose,(p,r)) := dite_eq_left h

theorem properties {J δ : ℝ} (hJ : 0<J) (hδ : 0≤δ) (hδ' : δ≤1/3)
    (hs : ∀a,A a → jump G a.2.1 a.1∈G.support ∧ jump G a.2.2 a.1∈G.support)
    (hu : ∀a,A a →
      jump G a.2.1 a.1*(G.w (G.point a.2.1)-G.w (G.center a.1))=1 ∧
      jump G a.2.2 a.1*(G.w (G.point a.2.2)-G.w (G.center a.1))=1)
    (hband : ∀a,A a → J≤height G a.2.1+height G a.2.2 ∧ height G a.2.1+height G a.2.2≤2*J)
    (herr : ∀a,A a → error G true a+error G false a≤δ*(height G a.2.1+height G a.2.2)) :
    (∀p r,edge A p r → p≠r ∧ label G A p r≠0 ∧ J/3≤exactHeight K (label G A p r) ∧
      (G.z (G.point p)-G.z (G.point r))*(G.w (G.point p)-G.w (G.point r))=
        2-label G A p r-(label G A p r)⁻¹) ∧
    (∀p p' r r',edge A p r → edge A p r' → edge A p' r → edge A p' r' →
      exactHeight K (label G A p r*label G A p' r'/(label G A p r'*label G A p' r))≤4*δ*J) := by
  have hns (a) (ha : A a) : jump G a.2.1 a.1≠0 ∧ jump G a.2.2 a.1≠0 :=
    ⟨left_ne_zero_of_mul_eq_one (hu a ha).1,left_ne_zero_of_mul_eq_one (hu a ha).2⟩
  have hE (a) (ha : A a) := selected G a hJ hδ hδ' (hns a ha).1 (hns a ha).2
    (hs a ha).1 (hs a ha).2 (hband a ha) (herr a ha)
  have hl (p r) (h : edge A p r) : label G A p r≠0 ∧ supported G.support (label G A p r) ∧
      l1 G (fun v => Real.log (av K v (label G A p r))+G.profile p v-G.profile r v)≤2*δ*J := by
    rw [label_eq G A h]
    exact ⟨div_ne_zero (hns _ h.choose_spec).1 (hns _ h.choose_spec).2,
      ratio_supported G _ (hns _ h.choose_spec).1 (hns _ h.choose_spec).2
        (hs _ h.choose_spec).1 (hs _ h.choose_spec).2,(hE _ h.choose_spec).2.2⟩
  constructor
  · intro p r h
    refine ⟨(hE _ h.choose_spec).1,(hl p r h).1,?_,?_⟩
    · rw [label_eq G A h]
      exact (hE _ h.choose_spec).2.1
    · rw [label_eq G A h]
      exact identity G _ (hu _ h.choose_spec).1 (hu _ h.choose_spec).2
  · intro p p' r r' h₁ h₂ h₃ h₄
    have hb := PlaceLogGeometry.rectangle G.support
      (label G A p r) (label G A p' r') (label G A p r') (label G A p' r)
      (hl p r h₁).1 (hl p' r' h₄).1 (hl p r' h₂).1 (hl p' r h₃).1
      (hl p r h₁).2.1 (hl p' r' h₄).2.1 (hl p r' h₂).2.1 (hl p' r h₃).2.1
      (G.profile p) (G.profile p') (G.profile r) (G.profile r')
      (hl p r h₁).2.2 (hl p' r' h₄).2.2 (hl p r' h₂).2.2 (hl p' r h₃).2.2
    linarith
end
end PlanarUnitDistances.OrganizedGraph

namespace PlanarUnitDistances.IncidenceSelected
open Filter Finset FiniteLaw FiniteStarCoupling IncidenceSequence IncidenceScale IncidenceBook
  IncidenceHeights OrganizedProfiles WeightedAbsoluteValues
open scoped Classical BigOperators
noncomputable section
variable {s : Sequence} {a : BudgetParameters.Params} {i : ℕ}
local instance : Fintype (s.P i⊕s.Q i) := inferInstance
local instance : Fintype (s.P i×s.Q i) := inferInstance
local instance : Fintype ((s.P i⊕s.Q i)→Bool) := labelFintype _
local instance : Fintype (LevelSnapshot.Data (s.P i⊕s.Q i) (s.P i×s.Q i)) := snapshotFintype _ _ _
def kept (R : Realization s a i) (J δ : ℝ) :=
  LawDeletion.keep (WedgeLaw.law (graph s i)) (IncidenceBand.band R J δ) (IncidencePopular.bad s i)
def edge (R : Realization s a i) (J δ : ℝ) := OrganizedGraph.edge (kept R J δ)
def label (R : Realization s a i) (J δ : ℝ) := OrganizedGraph.label R.input (kept R J δ)
def pairs (R : Realization s a i) (J δ : ℝ) := univ.filter (fun pr : s.P i×s.P i => edge R J δ pr.1 pr.2)

lemma properties (R : Realization s a i) {J δ : ℝ} (hJ : 0<J) (hδ : 0≤δ) (hδ' : δ≤1/3) :
    (∀p r,edge R J δ p r → p≠r ∧ label R J δ p r≠0 ∧ J/3≤exactHeight (model s i).field (label R J δ p r) ∧
      ((model s i).z (.inl p)-(model s i).z (.inl r))*((model s i).w (.inl p)-(model s i).w (.inl r))=
      2-label R J δ p r-(label R J δ p r)⁻¹) ∧
    (∀p p' r r',edge R J δ p r → edge R J δ p r' → edge R J δ p' r → edge R J δ p' r' →
      exactHeight (model s i).field (label R J δ p r*label R J δ p' r'/(label R J δ p r'*label R J δ p' r))≤4*δ*J) := by
  apply OrganizedGraph.properties R.input (kept R J δ) hJ hδ hδ'
  · intro x _
    exact ⟨(model s i).sub_mem (.inl x.2.1) (.inr x.1),(model s i).sub_mem (.inl x.2.2) (.inr x.1)⟩
  · intro x hx
    have hh := LawDeletion.wedge_support (graph s i) x hx.1
    exact ⟨(model s i).unit_identity _ _ (support s i _ _ hh.1),
      (model s i).unit_identity _ _ (support s i _ _ hh.2)⟩
  · intro x hx
    exact ⟨hx.2.1.1,hx.2.1.2.1⟩
  · intro x hx
    exact hx.2.1.2.2

lemma no_popular (R : Realization s a i) {J δ : ℝ} (p r : s.P i) (he : edge R J δ p r) :
    ∀c∈IncidencePopular.centers s i,¬(dist (UnitCodegree.zCoordinate p.val) c=1 ∧
      dist (UnitCodegree.zCoordinate r.val) c=1) := by
  obtain ⟨q,hq⟩ := he
  intro c hc h
  exact hq.2.2 ⟨c,hc,h.1,h.2⟩

lemma count (R : Realization s a i) {J δ : ℝ} (hJ : 0<J) (hδ : 0≤δ) (hδ' : δ≤1/3) :
    event (WedgeLaw.law (graph s i)) (kept R J δ) *
      (CircleIncidence.incidences (s.P i) (s.Q i)*((27/50:ℝ)*CircleIncidence.incidences (s.P i) (s.Q i)/(s.Q i).card)/2) ≤ (pairs R J δ).card := by
  have he := (s.good i).positive
  have hc : 0<((s.Q i).card:ℝ) := Nat.cast_pos.mpr (GeometricLaw.card_pos _ _ he).2
  have hd : 0<(27/50:ℝ)*CircleIncidence.incidences (s.P i) (s.Q i)/(s.Q i).card := by positivity
  have hdeg (q : s.Q i) : (27/50:ℝ)*CircleIncidence.incidences (s.P i) (s.Q i)/(s.Q i).card≤
      IncidenceEntropy.degree (GeometricLaw.E (s.P i) (s.Q i)) q := by
    rw [GeometricLaw.degree_eq]
    have hh := (le_div_iff₀ he).mp ((s.good i).atomQ q q.property)
    simpa only [div_mul_eq_mul_div] using hh
  have hcodeg := IncidenceEntropy.unit_incidence_codegree (GeometricLaw.E (s.P i) (s.Q i))
    (fun p => UnitCodegree.zCoordinate p.val) (fun q => UnitCodegree.zCoordinate q.val)
    (UnitCodegree.zCoordinate.injective.comp Subtype.val_injective)
    (UnitCodegree.zCoordinate.injective.comp Subtype.val_injective)
    (fun p q h => by rw [UnitCodegree.zCoordinate.dist_map]; exact h)
  have hb := UniformGraphLaw.edge_count (GeometricLaw.E (s.P i) (s.Q i))
    (by rw [GeometricLaw.edgeCount_eq]; exact he) hd hdeg hcodeg (kept R J δ)
    (fun x hx => (properties R hJ hδ hδ').1 x.2.1 x.2.2 ⟨x.1,hx⟩ |>.1)
  have hb' : event (WedgeLaw.law (graph s i)) (kept R J δ)≤
    ((pairs R J δ).card:ℝ)*2/(IncidenceEntropy.edgeCount (GeometricLaw.E (s.P i) (s.Q i))*((27/50:ℝ)*CircleIncidence.incidences (s.P i) (s.Q i)/(s.Q i).card)) := by
    convert hb using 1
    all_goals simp only [graph,GeometricLaw.graph,pairs,edge,OrganizedGraph.edge,Prod.eta]
    all_goals congr 8
  rw [GeometricLaw.edgeCount_eq] at hb'
  have hh := (le_div_iff₀ (mul_pos he hd)).mp hb'
  nlinarith

theorem choose (s : Sequence) : ∃c : ℝ,0<c ∧ ∀δ : ℝ,0<δ → δ≤1/3 →
    ∃a : BudgetParameters.Params,∃b : ℝ,0<b ∧ ∀ᶠi in atTop,∃R : Realization s a i,∃J : ℝ,
      0<J ∧ c*scale s i/2≤J ∧
      b*(CircleIncidence.incidences (s.P i) (s.Q i)*((27/50:ℝ)*CircleIncidence.incidences (s.P i) (s.Q i)/(s.Q i).card)/2)≤(pairs R J δ).card := by
  obtain ⟨c,hc,h⟩ := IncidenceBand.choose s
  refine ⟨c,hc,?_⟩
  intro δ hδ hδ'
  obtain ⟨a,b,hb,h⟩ := h δ hδ
  refine ⟨a,b/2,by positivity,?_⟩
  filter_upwards [h,(IncidencePopular.cost_limit s).eventually_le_const (by positivity : 0<b/2),
    (scale_limit s).eventually_gt_atTop 0] with i hi hcost hscale
  obtain ⟨R,J,hJ,hband⟩ := hi
  have hJ0 : 0<J := lt_of_lt_of_le (by positivity) hJ
  refine ⟨R,J,hJ0,hJ,?_⟩
  have hkeep := LawDeletion.cost (WedgeLaw.law (graph s i)) (IncidenceBand.band R J δ) (IncidencePopular.bad s i)
  change event (WedgeLaw.law (graph s i)) (IncidenceBand.band R J δ)≤
    event (WedgeLaw.law (graph s i)) (kept R J δ)+event (WedgeLaw.law (graph s i)) (IncidencePopular.bad s i) at hkeep
  have hp : b/2≤event (WedgeLaw.law (graph s i)) (kept R J δ) := by linarith
  have he := (s.good i).positive
  exact (mul_le_mul_of_nonneg_right hp (by positivity)).trans (count R hJ0 hδ.le hδ')
end
end PlanarUnitDistances.IncidenceSelected

namespace PlanarUnitDistances.ImageRelation
open Finset
open scoped Classical
noncomputable section
variable {α β K : Type*}
variable (P : Finset α) (f : α → β) (hf : Function.Injective f)
def image : Finset β := P.image f
def equiv : P ≃ image P f where
  toFun p := ⟨f p,mem_image.mpr ⟨p,p.property,rfl⟩⟩
  invFun p := ⟨(mem_image.mp p.property).choose,(mem_image.mp p.property).choose_spec.1⟩
  left_inv p := Subtype.ext (hf (mem_image.mp (show f p∈P.image f from mem_image.mpr ⟨p,p.property,rfl⟩)).choose_spec.2)
  right_inv p := Subtype.ext (mem_image.mp p.property).choose_spec.2
lemma equiv_val (p : P) : ((equiv P f hf p):β)=f p := rfl
lemma inv_val (p : image P f) : f ((equiv P f hf).symm p)=p :=
  congrArg Subtype.val ((equiv P f hf).apply_symm_apply p)
variable (E : P → P → Prop) (l : P → P → K) [One K]
def edge (p r : β) : Prop := ∃hp : p∈image P f,∃hr : r∈image P f,
  E ((equiv P f hf).symm ⟨p,hp⟩) ((equiv P f hf).symm ⟨r,hr⟩)
def label (p r : β) : K := if hp : p∈image P f then if hr : r∈image P f then
  l ((equiv P f hf).symm ⟨p,hp⟩) ((equiv P f hf).symm ⟨r,hr⟩) else 1 else 1
lemma edge_iff (p r : image P f) : edge P f hf E p r ↔
    E ((equiv P f hf).symm p) ((equiv P f hf).symm r) := by
  constructor
  · rintro ⟨hp,hr,h⟩; exact h
  · intro h; exact ⟨p.property,r.property,h⟩
lemma label_eq (p r : image P f) : label P f hf l p r=
    l ((equiv P f hf).symm p) ((equiv P f hf).symm r) := by
  simp only [label,p.property,r.property,↓reduceDIte]
lemma card : (univ.filter (fun pr : image P f×image P f => edge P f hf E pr.1 pr.2)).card=
    (univ.filter (fun pr : P×P => E pr.1 pr.2)).card := by
  apply card_bij (fun pr _ => ((equiv P f hf).symm pr.1,(equiv P f hf).symm pr.2))
  · intro pr hpr
    exact mem_filter.mpr ⟨mem_univ _,(edge_iff P f hf E _ _).mp (mem_filter.mp hpr).2⟩
  · intro pr _ qr _ h
    apply Prod.ext
    · exact (equiv P f hf).symm.injective (congrArg Prod.fst h)
    · exact (equiv P f hf).symm.injective (congrArg Prod.snd h)
  · intro pr hpr
    refine ⟨(equiv P f hf pr.1,equiv P f hf pr.2),?_,?_⟩
    · apply mem_filter.mpr
      refine ⟨mem_univ _,(edge_iff P f hf E _ _).mpr ?_⟩
      simpa only [Equiv.symm_apply_apply] using (mem_filter.mp hpr).2
    · simp
end
end PlanarUnitDistances.ImageRelation

namespace PlanarUnitDistances.IncidenceComplex
open Finset IncidenceSequence IncidenceScale IncidenceBook IncidenceSelected
open scoped Classical
noncomputable section
variable {s : Sequence} {a : BudgetParameters.Params} {i : ℕ}
def pull (p : IncidencePopular.points s i) : s.P i :=
  (ImageRelation.equiv (s.P i) UnitCodegree.zCoordinate UnitCodegree.zCoordinate.injective).symm p
lemma pull_coord (p : IncidencePopular.points s i) : UnitCodegree.zCoordinate (pull p).val=p :=
  ImageRelation.inv_val _ _ _ p

def edge (R : Realization s a i) (J δ : ℝ) : ℂ → ℂ → Prop :=
  ImageRelation.edge (s.P i) UnitCodegree.zCoordinate UnitCodegree.zCoordinate.injective (IncidenceSelected.edge R J δ)
def label (R : Realization s a i) (J δ : ℝ) : ℂ → ℂ → (model s i).field :=
  ImageRelation.label (s.P i) UnitCodegree.zCoordinate UnitCodegree.zCoordinate.injective (IncidenceSelected.label R J δ)
lemma edge_iff (R : Realization s a i) (J δ : ℝ) (p r : IncidencePopular.points s i) :
    edge R J δ p r ↔ IncidenceSelected.edge R J δ (pull p) (pull r) := ImageRelation.edge_iff _ _ _ _ p r
lemma label_eq (R : Realization s a i) (J δ : ℝ) (p r : IncidencePopular.points s i) :
    label R J δ p r=IncidenceSelected.label R J δ (pull p) (pull r) := ImageRelation.label_eq _ _ _ _ p r
lemma card (R : Realization s a i) (J δ : ℝ) :
    (univ.filter (fun pr : IncidencePopular.points s i×IncidencePopular.points s i => edge R J δ pr.1 pr.2)).card=
    (pairs R J δ).card := ImageRelation.card _ _ _ _
lemma z_pull (p : IncidencePopular.points s i) : ((model s i).z (.inl (pull p)):ℂ)=p := by
  rw [(model s i).z_eq]
  exact pull_coord p
lemma w_pull (p : IncidencePopular.points s i) : ((model s i).w (.inl (pull p)):ℂ)=star p.val := by
  rw [(model s i).w_eq]
  exact congrArg star (pull_coord p)
lemma nonzero (R : Realization s a i) {J δ : ℝ} (hJ : 0<J) (hδ : 0≤δ) (hδ' : δ≤1/3)
    (p r : IncidencePopular.points s i) (he : edge R J δ p r) : label R J δ p r≠0 := by
  rw [label_eq]
  exact (IncidenceSelected.properties R hJ hδ hδ').1 _ _ ((edge_iff R J δ p r).mp he) |>.2.1
lemma large (R : Realization s a i) {J δ : ℝ} (hJ : 0<J) (hδ : 0≤δ) (hδ' : δ≤1/3)
    (p r : IncidencePopular.points s i) (he : edge R J δ p r) :
    J/3≤WeightedAbsoluteValues.exactHeight (model s i).field (label R J δ p r) := by
  rw [label_eq]
  exact (IncidenceSelected.properties R hJ hδ hδ').1 _ _ ((edge_iff R J δ p r).mp he) |>.2.2.1
lemma distance (R : Realization s a i) {J δ : ℝ} (hJ : 0<J) (hδ : 0≤δ) (hδ' : δ≤1/3)
    (p r : IncidencePopular.points s i) (he : edge R J δ p r) :
    (p.val-r.val)*(star p.val-star r.val)=2-(label R J δ p r:ℂ)-(label R J δ p r:ℂ)⁻¹ := by
  have h := (IncidenceSelected.properties R hJ hδ hδ').1 _ _ ((edge_iff R J δ p r).mp he) |>.2.2.2
  have hh := congrArg (model s i).field.val h
  simp only [map_mul,map_sub,map_ofNat,map_inv₀] at hh
  simpa only [IntermediateField.coe_val,←label_eq R J δ p r,z_pull,w_pull] using hh
lemma rectangle (R : Realization s a i) {J δ : ℝ} (hJ : 0<J) (hδ : 0≤δ) (hδ' : δ≤1/3)
    (p p' r r' : IncidencePopular.points s i) (h₁ : edge R J δ p r) (h₂ : edge R J δ p r')
    (h₃ : edge R J δ p' r) (h₄ : edge R J δ p' r') :
    WeightedAbsoluteValues.exactHeight (model s i).field
      (label R J δ p r*label R J δ p' r'/(label R J δ p r'*label R J δ p' r))≤4*δ*J := by
  simp only [label_eq]
  exact (IncidenceSelected.properties R hJ hδ hδ').2 _ _ _ _
    ((edge_iff R J δ p r).mp h₁) ((edge_iff R J δ p r').mp h₂)
    ((edge_iff R J δ p' r).mp h₃) ((edge_iff R J δ p' r').mp h₄)
lemma no_circle (R : Realization s a i) {J δ : ℝ} (hk : 2≤IncidencePopular.k s i)
    (p r : IncidencePopular.points s i) (he : edge R J δ p r) (c : ℂ)
    (hc : s.t i^(9/10:ℝ)≤((IncidencePopular.points s i).filter (fun v => ‖v-c‖=1)).card) :
    ¬(‖p.val-c‖=1 ∧ ‖r.val-c‖=1) := by
  have hcount : IncidencePopular.k s i≤(PopularCircles.neighbors (IncidencePopular.points s i) c).card := by
    apply Nat.ceil_le.mpr
    simpa only [PopularCircles.neighbors,dist_eq_norm] using hc
  have hh := IncidenceSelected.no_popular R (pull p) (pull r) ((edge_iff R J δ p r).mp he)
    c ((PopularCircles.mem_popular hk).mpr hcount)
  simpa only [pull_coord,dist_eq_norm] using hh
end
end PlanarUnitDistances.IncidenceComplex

end OAI
