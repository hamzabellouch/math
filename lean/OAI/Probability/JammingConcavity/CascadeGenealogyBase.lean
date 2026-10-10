import Mathlib
import OAI.Probability.JammingConcavity.FamilyCascadeLog

namespace OAI

/-! Cascade Genealogy Base. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open Set Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory Filter Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
open scoped NNReal ENNReal Topology
open scoped NNReal Topology
open Set
open Set Filter MeasureTheory
open scoped BigOperators
open scoped Topology NNReal
open scoped Topology BigOperators
open scoped ENNReal NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming

lemma weightTreeLaw_probability (k : ℕ) : IsProbabilityMeasure (weightTreeLaw k) := by
  induction k with
  | zero => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac ()))
  | succ k ih =>
    let := ih
    exact inferInstanceAs (IsProbabilityMeasure
      ((pointCloudLaw (weightTreeLaw k)).map pointCloudMeasure))

lemma familyCascadeLaw_probability {E : Type} [MeasurableSpace E] (k : ℕ) (ν : ℕ → Measure E)
    (hν : ∀ j, IsProbabilityMeasure (ν j)) : IsProbabilityMeasure (familyCascadeLaw k ν) := by
  induction k generalizing ν with
  | zero => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac ()))
  | succ k ih =>
    let := hν 0
    let := ih (fun j => ν (j+1)) (fun j => hν (j+1))
    exact inferInstanceAs (IsProbabilityMeasure (pointCloudLaw ((ν 0).prod
      (familyCascadeLaw k (fun j => ν (j+1))))))

lemma measurable_familyRecursion {E : Type} [MeasurableSpace E] [Add E] [MeasurableAdd₂ E]
    (ms : List ℝ) (ν : ℕ → Measure E) (hν : ∀ j, IsProbabilityMeasure (ν j))
    {u : E → ℝ} (hu : Measurable u) : Measurable (familyRecursion ms ν u) := by
  induction ms generalizing ν with
  | nil => exact hu
  | cons m ms ih =>
    let := hν 0
    have ht := ih (fun j => ν (j+1)) (fun j => hν (j+1))
    have he : Measurable (fun z : E × E => Real.exp
        (m*familyRecursion ms (fun j => ν (j+1)) u (z.1+z.2))) := by fun_prop
    exact (Real.measurable_log.comp he.stronglyMeasurable.integral_prod_right'.measurable).const_mul _

lemma measurable_familyEdgeMultiplier {E : Type} [MeasurableSpace E] [Add E] [MeasurableAdd₂ E]
    (m : ℝ) (ms : List ℝ) (ν : ℕ → Measure E) (hν : ∀ j, IsProbabilityMeasure (ν j))
    {u : E → ℝ} (hu : Measurable u) :
    Measurable (fun z : E × E => familyEdgeMultiplier m ms ν u z.1 z.2) := by
  have h₁ := measurable_familyRecursion ms (fun j => ν (j+1)) (fun j => hν (j+1)) hu
  have h₂ := measurable_familyRecursion (m::ms) ν hν hu
  unfold familyEdgeMultiplier
  fun_prop

lemma familyEdgeMultiplier_moment {E : Type} [MeasurableSpace E] [Add E]
    {m : ℝ} (hm : m ≠ 0) (ms : List ℝ) (ν : ℕ → Measure E) (hν : ∀ j, IsProbabilityMeasure (ν j))
    (u : E → ℝ) (hi : FamilyMomentsFinite (m::ms) ν u) (x : E) :
    Integrable (fun a => (familyEdgeMultiplier m ms ν u x a)^m) (ν 0) ∧
    (∫ a, (familyEdgeMultiplier m ms ν u x a)^m ∂ν 0) = 1 := by
  let := hν 0
  let c := ∫ a, Real.exp (m*familyRecursion ms (fun j => ν (j+1)) u (x+a)) ∂ν 0
  have hc : 0 < c := integral_exp_pos (hi.1 x)
  have he (a : E) : (familyEdgeMultiplier m ms ν u x a)^m =
      Real.exp (m*familyRecursion ms (fun j => ν (j+1)) u (x+a))/c := by
    change (Real.exp (familyRecursion ms (fun j => ν (j+1)) u (x+a) -
      (1/m)*Real.log c))^m = _
    rw [← Real.exp_mul, show (familyRecursion ms (fun j => ν (j+1)) u (x+a) -
        (1/m)*Real.log c)*m = m*familyRecursion ms (fun j => ν (j+1)) u (x+a)-Real.log c by field_simp,
      Real.exp_sub, Real.exp_log hc]
  refine ⟨?_, ?_⟩
  · simp_rw [he]
    exact (hi.1 x).div_const c
  · simp_rw [he]
    rw [integral_div]
    exact div_self hc.ne'

end MicroscopicJamming

 
 
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming
lemma pointCloudMeasure_pushforward {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {f : A → B} (hf : Measurable f) (ω : PointCloud A) :
    pointCloudMeasure (mapPointCloud f ω) =
      (pointCloudMeasure ω).map (Prod.map id f) := by
  classical
  have hF : Measurable (Prod.map (id : ℝ → ℝ) f) := measurable_id.prodMap hf
  unfold pointCloudMeasure
  rw [Measure.map_sum hF.aemeasurable]
  congr 1
  funext n
  rw [Measure.map_sum hF.aemeasurable]
  congr 1
  funext j
  change (if j < (ω n).1 then Measure.dirac _ else 0) =
    Measure.map (Prod.map id f) (if j < (ω n).1 then Measure.dirac _ else 0)
  split_ifs
  · rw [Measure.map_dirac' hF]
    rfl
  · exact (Measure.map_zero _).symm

lemma measurable_parameterized_cloud_map {P A B : Type*}
    [MeasurableSpace P] [MeasurableSpace A] [MeasurableSpace B]
    {f : P × (ℝ × A) → B} (hf : Measurable f) :
    Measurable (fun z : P × PointCloud A =>
      (pointCloudMeasure z.2).map (fun a => f (z.1,a))) := by
  classical
  have he (z : P × PointCloud A) :
      (pointCloudMeasure z.2).map (fun a => f (z.1,a)) =
      Measure.sum (fun n => Measure.sum (fun j =>
        if j < (z.2 n).1 then Measure.dirac
          (f (z.1,((n:ℝ)+((z.2 n).2 j).1,((z.2 n).2 j).2))) else 0)) := by
    have h : Measurable (fun a => f (z.1,a)) := hf.comp (measurable_const.prodMk measurable_id)
    unfold pointCloudMeasure
    rw [Measure.map_sum h.aemeasurable]
    congr 1
    funext n
    rw [Measure.map_sum h.aemeasurable]
    congr 1
    funext j
    split_ifs
    · rw [Measure.map_dirac' h]
    · exact Measure.map_zero _
  simp_rw [he]
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [Measure.sum_apply _ hs]
  apply Measurable.tsum
  intro n
  apply Measurable.tsum
  intro j
  have ht : MeasurableSet {z : P × PointCloud A | j < (z.2 n).1} := by measurability
  exact (Measure.measurable_coe hs).comp
    ((Measure.measurable_dirac.comp (hf.comp (by fun_prop))).ite ht measurable_const)
end MicroscopicJamming
namespace MicroscopicJamming
lemma pointCloudMeasure_markLaw {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (ν : Measure A) [IsProbabilityMeasure ν] {f : A → B} (hf : Measurable f) :
    (pointCloudLaw ν).map (fun ω => (pointCloudMeasure ω).map (Prod.map id f)) =
    (pointCloudLaw (ν.map f)).map pointCloudMeasure := by
  rw [← pointCloudLaw_map ν hf, Measure.map_map measurable_pointCloudMeasure
    (measurable_mapPointCloud hf)]
  congr 1
  funext ω
  exact (pointCloudMeasure_pushforward hf ω).symm
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming
lemma measurable_transformedWeightTree {E : Type} [MeasurableSpace E] [Add E] [MeasurableAdd₂ E]
    (ms : List ℝ) (ν : ℕ → Measure E) (hν : ∀ j, IsProbabilityMeasure (ν j))
    {u : E → ℝ} (hu : Measurable u) :
    Measurable (fun z : E × FamilyCascadeTree E ms.length => transformedWeightTree ms ν u z.1 z.2) := by
  induction ms generalizing ν with
  | nil => exact measurable_const
  | cons m ms ih =>
    have ht := ih (fun j => ν (j+1)) (fun j => hν (j+1))
    have hc := measurable_familyEdgeMultiplier m ms ν hν hu
    change Measurable (fun z : E × PointCloud (E × FamilyCascadeTree E ms.length) =>
      (pointCloudMeasure z.2).map (fun a =>
        (a.1/(familyEdgeMultiplier m ms ν u z.1 a.2.1)^m,
          transformedWeightTree ms (fun j => ν (j+1)) u (z.1+a.2.1) a.2.2)))
    apply measurable_parameterized_cloud_map (f := fun z : E × (ℝ × (E × FamilyCascadeTree E ms.length)) =>
      (z.2.1/(familyEdgeMultiplier m ms ν u z.1 z.2.2.1)^m,
        transformedWeightTree ms (fun j => ν (j+1)) u (z.1+z.2.2.1) z.2.2.2))
    exact (measurable_snd.fst.div ((hc.comp (measurable_fst.prodMk
      measurable_snd.snd.fst)).pow_const _)).prodMk
      (ht.comp ((measurable_fst.add measurable_snd.snd.fst).prodMk measurable_snd.snd.snd))
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming
lemma pointCloudTilt_prod {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (ν : Measure A) (μ : Measure B) [SFinite μ] (m : ℝ)
    {c : A → ℝ} (hc : Measurable c) :
    pointCloudTilt m (fun z : A × B => c z.1) (ν.prod μ) =
      (pointCloudTilt m c ν).prod μ := by
  have h : Measurable (fun a => ENNReal.ofReal ((c a)^m)) := (hc.pow_const _).ennreal_ofReal
  exact (prod_withDensity_left (μ := ν) (ν := μ) h).symm

lemma pointCloud_scaled_forget_law {A B : Type} [MeasurableSpace A] [MeasurableSpace B]
    (ν : Measure A) (μ : Measure B) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {m : ℝ} (hm : 0 < m) (hm1 : m < 1) {c : A → ℝ} (hc : Measurable c)
    (hcpos : ∀ a, 0 < c a) (hi : Integrable (fun a => (c a)^m) ν)
    (he : (∫ a, (c a)^m ∂ν) = 1) :
    (pointCloudLaw (ν.prod μ)).map (fun ω => (pointCloudMeasure ω).map
      (fun z : ℝ × (A × B) => (z.1/(c z.2.1)^m,z.2.2))) =
    (pointCloudLaw μ).map pointCloudMeasure := by
  have hi' : Integrable (fun z : A × B => (c z.1)^m) (ν.prod μ) := hi.comp_fst μ
  have he' : (∫ z : A × B, (c z.1)^m ∂ν.prod μ) = 1 := by
    simpa using (integral_prod_mul (μ := ν) (ν := μ) (fun a => (c a)^m) (fun _ => (1:ℝ))).trans
      (by simp [he])
  have hmark := (pointCloudMeasureMarking (A × B) inferInstance (ν.prod μ) inferInstance
    m hm hm1 (fun z => c z.1) (hc.comp measurable_fst) (fun z => hcpos z.1) hi' he').2
  have hprob := pointCloudTilt_probability ν m c hcpos hi he
  let := hprob
  let T : ℝ × (A × B) → ℝ × (A × B) := fun z => (z.1/(c z.2.1)^m,z.2)
  let F : ℝ × (A × B) → ℝ × B := Prod.map id Prod.snd
  have hT : Measurable T := (measurable_fst.div ((hc.comp measurable_snd.fst).pow_const _)).prodMk measurable_snd
  have hF : Measurable F := measurable_id.prodMap measurable_snd
  have hmap : Measurable (fun ω : PointCloud (A × B) => (pointCloudMeasure ω).map T) :=
    (Measure.measurable_map T hT).comp measurable_pointCloudMeasure
  have hresult := congrArg (fun ρ : Measure (Measure (ℝ × (A × B))) =>
    ρ.map (fun η => η.map F)) hmark
  rw [Measure.map_map (Measure.measurable_map F hF) hmap,
    Measure.map_map (Measure.measurable_map F hF) measurable_pointCloudMeasure] at hresult
  have hcomp (ω : PointCloud (A × B)) :
      ((pointCloudMeasure ω).map T).map F =
        (pointCloudMeasure ω).map (fun z => (z.1/(c z.2.1)^m,z.2.2)) := by
    rw [Measure.map_map hF hT]
    rfl
  change (pointCloudLaw (ν.prod μ)).map (fun ω => ((pointCloudMeasure ω).map T).map F) =
    (pointCloudLaw (pointCloudTilt m (fun z : A × B => c z.1) (ν.prod μ))).map
      (fun ω => (pointCloudMeasure ω).map F) at hresult
  simp_rw [hcomp] at hresult
  rw [pointCloudTilt_prod ν μ m hc] at hresult
  change _ = (pointCloudLaw ((pointCloudTilt m c ν).prod μ)).map
    (fun ω => (pointCloudMeasure ω).map (Prod.map id Prod.snd)) at hresult
  rw [pointCloudMeasure_markLaw _ measurable_snd] at hresult
  simpa [Measure.map_snd_prod, measure_univ] using hresult
end MicroscopicJamming

 
 
open MeasureTheory Set

lemma map_fiber_product {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] (ν : Measure A) (μ : Measure B) [SFinite μ]
    (ρ : Measure C) [SFinite ρ] {f : A × B → C} (hf : Measurable f)
    (hlaw : ∀ a, μ.map (fun b => f (a,b)) = ρ) :
    (ν.prod μ).map (fun z => (z.1,f z)) = ν.prod ρ := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (measurable_fst.prodMk hf) hs,
    Measure.prod_apply ((measurable_fst.prodMk hf) hs), Measure.prod_apply hs]
  apply lintegral_congr
  intro a
  have hfa : Measurable (fun b => f (a,b)) := hf.comp (measurable_const.prodMk measurable_id)
  rw [← hlaw a, Measure.map_apply hfa (measurable_prodMk_left hs)]
  rfl

 
 

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming

theorem cascadeGenealogy : CascadeGenealogyStatement := by
  intro E mem ad madd ms hms hb ν hν u hu hi x
  induction ms generalizing ν x with
  | nil =>
    change (Measure.dirac ()).map (fun _ : Unit => ()) = Measure.dirac ()
    rw [Measure.map_dirac' measurable_const]
  | cons m ms ih =>
    have hm : 0 < m := (hb m (by simp)).1
    have hm1 : m < 1 := (hb m (by simp)).2
    have hms' := hms.tail
    have hb' : ∀ a ∈ ms, 0 < a ∧ a < 1 := fun a ha => hb a (by simp [ha])
    let ν' : ℕ → Measure E := fun j => ν (j+1)
    let μ := familyCascadeLaw ms.length ν'
    let ρ := weightTreeLaw ms.length
    let : IsProbabilityMeasure μ := familyCascadeLaw_probability _ _ (fun j => hν (j+1))
    let : IsProbabilityMeasure ρ := weightTreeLaw_probability _
    let : IsProbabilityMeasure (ν 0) := hν 0
    let f : E × FamilyCascadeTree E ms.length → WeightTree ms.length :=
      fun z => transformedWeightTree ms ν' u (x+z.1) z.2
    have hf : Measurable f := (measurable_transformedWeightTree ms ν'
      (fun j => hν (j+1)) hu).comp
      ((measurable_const.add measurable_fst).prodMk measurable_snd)
    have hlaw : ∀ a, μ.map (fun b => f (a,b)) = ρ := by
      intro a
      exact ih hms' hb' ν' (fun j => hν (j+1)) hi.2 (x+a)
    let F : E × FamilyCascadeTree E ms.length → E × WeightTree ms.length := fun z => (z.1,f z)
    have hF : Measurable F := measurable_fst.prodMk hf
    have hFlaw : ((ν 0).prod μ).map F = (ν 0).prod ρ := map_fiber_product _ _ _ hf hlaw
    let c : E → ℝ := familyEdgeMultiplier m ms ν u x
    have hc : Measurable c := (measurable_familyEdgeMultiplier m ms ν hν hu).comp
      (measurable_const.prodMk measurable_id)
    have hcpos : ∀ a, 0 < c a := fun a => Real.exp_pos _
    have hcm := familyEdgeMultiplier_moment hm.ne' ms ν hν u hi x
    let G : ℝ × (E × WeightTree ms.length) → ℝ × WeightTree ms.length :=
      fun z => (z.1/(c z.2.1)^m,z.2.2)
    have hG : Measurable G := (measurable_fst.div ((hc.comp measurable_snd.fst).pow_const _)).prodMk
      measurable_snd.snd
    let root : PointCloud (E × WeightTree ms.length) → Measure (ℝ × WeightTree ms.length) :=
      fun ω => (pointCloudMeasure ω).map G
    have hroot : Measurable root := (Measure.measurable_map G hG).comp measurable_pointCloudMeasure
    have hpoint : transformedWeightTree (m::ms) ν u x = root ∘ mapPointCloud F := by
      funext ω
      change transformedWeightTree (m::ms) ν u x ω = (pointCloudMeasure (mapPointCloud F ω)).map G
      have hp := congrArg (fun η : Measure (ℝ × (E × WeightTree ms.length)) => η.map G)
        (pointCloudMeasure_pushforward hF ω)
      exact (hp.trans (Measure.map_map hG (measurable_id.prodMap hF))).symm
    have hfinal : ((pointCloudLaw ((ν 0).prod μ)).map (mapPointCloud F)).map root =
        (pointCloudLaw ρ).map pointCloudMeasure := by
      rw [pointCloudLaw_map _ hF, hFlaw]
      exact pointCloud_scaled_forget_law (ν 0) ρ hm hm1 hc hcpos hcm.1 hcm.2
    have heq := (Measure.map_map hroot (measurable_mapPointCloud hF)).symm.trans hfinal
    have hcong : (pointCloudLaw ((ν 0).prod μ)).map (transformedWeightTree (m::ms) ν u x) =
        (pointCloudLaw ((ν 0).prod μ)).map (root ∘ mapPointCloud F) :=
      Measure.map_congr (Filter.Eventually.of_forall (fun ω => congrFun hpoint ω))
    exact hcong.trans heq
end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace MicroscopicJamming

def CascadeMarkTree (E : Type) : ℕ → Type
  | 0 => Unit
  | k+1 => ℕ → ℕ → E × CascadeMarkTree E k

instance cascadeMarkMeasurable (E : Type) [MeasurableSpace E] :
    (k : ℕ) → MeasurableSpace (CascadeMarkTree E k)
  | 0 => inferInstanceAs (MeasurableSpace Unit)
  | k+1 => by
    letI := cascadeMarkMeasurable E k
    exact inferInstanceAs (MeasurableSpace (ℕ → ℕ → E × CascadeMarkTree E k))

def cascadeMarkLaw {E : Type} [MeasurableSpace E] :
    (k : ℕ) → (ℕ → Measure E) → Measure (CascadeMarkTree E k)
  | 0, _ => Measure.dirac ()
  | k+1, ν => Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ =>
    (ν 0).prod (cascadeMarkLaw k (fun j => ν (j+1)))

instance cascadeMarkLaw_probability {E : Type} [MeasurableSpace E]
    (k : ℕ) (ν : ℕ → Measure E) [∀ j, IsProbabilityMeasure (ν j)] :
    IsProbabilityMeasure (cascadeMarkLaw k ν) := by
  induction k generalizing ν with
  | zero => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac ()))
  | succ k ih =>
    let := ih (fun j => ν (j+1))
    exact inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi fun _ : ℕ =>
      Measure.infinitePi fun _ : ℕ => (ν 0).prod (cascadeMarkLaw k (fun j => ν (j+1)))))

def zipCascade {E : Type} : (k : ℕ) →
    CascadeTree k × CascadeMarkTree E k → FamilyCascadeTree E k
  | 0, _ => ()
  | k+1, p => mapPointCloud (fun z => (z.2.1, zipCascade k (z.1,z.2.2))) (zipPointCloud p)

lemma measurable_zipCascade {E : Type} [MeasurableSpace E] (k : ℕ) :
    Measurable (zipCascade (E := E) k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    exact (measurable_mapPointCloud ((measurable_fst.comp measurable_snd).prodMk
      (ih.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))))).comp
      measurable_zipPointCloud

lemma prod_rotate_map {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] (μ : Measure A) (ν : Measure B) (ρ : Measure C)
    [SFinite μ] [SFinite ν] [SFinite ρ] :
    (μ.prod (ν.prod ρ)).map (fun z => (z.2.1,(z.1,z.2.2))) = ν.prod (μ.prod ρ) := by
  have H := (measurePreserving_prodAssoc ν μ ρ).comp
    ((Measure.measurePreserving_swap (μ := μ) (ν := ν)).prod (MeasurePreserving.id ρ))
  have H' := H.comp (measurePreserving_prodAssoc μ ν ρ).symm
  exact H'.map_eq

theorem cascade_independent_marks {E : Type} [MeasurableSpace E] (ms : List ℝ)
    (ν : ℕ → Measure E) [∀ j, IsProbabilityMeasure (ν j)] :
    ((cascadeLaw ms).prod (cascadeMarkLaw ms.length ν)).map (zipCascade ms.length) =
      familyCascadeLaw ms.length ν := by
  induction ms generalizing ν with
  | nil =>
    change Measure.map (fun _ : Unit × Unit => ())
      ((Measure.dirac ()).prod (Measure.dirac ())) = Measure.dirac ()
    rw [Measure.dirac_prod_dirac, Measure.map_dirac]
  | cons m ms ih =>
    let ρ := cascadeLaw ms
    let η := cascadeMarkLaw ms.length (fun j => ν (j+1))
    let F : CascadeTree ms.length × (E × CascadeMarkTree E ms.length) →
        E × FamilyCascadeTree E ms.length := fun z => (z.2.1,zipCascade ms.length (z.1,z.2.2))
    have hF : Measurable F := (measurable_fst.comp measurable_snd).prodMk
      ((measurable_zipCascade ms.length).comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
    have hFlaw : (ρ.prod ((ν 0).prod η)).map F = (ν 0).prod
        (familyCascadeLaw ms.length (fun j => ν (j+1))) := by
      rw [show F = (Prod.map id (zipCascade ms.length)) ∘
        (fun z : CascadeTree ms.length × (E × CascadeMarkTree E ms.length) => (z.2.1,(z.1,z.2.2))) from rfl,
        ← Measure.map_map (measurable_id.prodMap (measurable_zipCascade ms.length)) (by fun_prop), prod_rotate_map,
        ← Measure.map_prod_map _ _ measurable_id (measurable_zipCascade ms.length), Measure.map_id]
      rw [ih]
    change (((pointCloudLaw ρ).prod
      (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => (ν 0).prod η)).map
      ((mapPointCloud F) ∘ zipPointCloud)) = _
    rw [← Measure.map_map (measurable_mapPointCloud hF) measurable_zipPointCloud,
      pointCloud_independent_marks, pointCloudLaw_map _ hF, hFlaw]
    rfl
end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MicroscopicJamming

def spinI : List ℝ → (ℕ → ℝ≥0) → ℝ
  | [], _ => 0
  | m::ms, d => m*d 0 + spinI ms (fun j => d (j+1))

def spinLambda (ms : List ℝ) (d : ℕ → ℝ≥0) (b : ℝ) : ℝ := b-spinI ms d

def spinC : List ℝ → (ℕ → ℝ≥0) → ℝ → ℝ
  | [], _, b => -(1/2)*Real.log b
  | m::ms, d, b => spinC ms (fun j => d (j+1)) b + (1/(2*m))*
      Real.log (spinLambda ms (fun j => d (j+1)) b / spinLambda (m::ms) d b)

def spinV : List ℝ → (ℕ → ℝ≥0) → ℝ → ℝ
  | [], _, _ => 0
  | m::ms, d, b => (d 0:ℝ)/(spinLambda ms (fun j => d (j+1)) b * spinLambda (m::ms) d b) +
      spinV ms (fun j => d (j+1)) b

def spinTerminal (b : ℝ) (z : ℝ) : ℝ := -(1/2)*Real.log b + z^2/(2*b)

def spinIncrementLaw (d : ℕ → ℝ≥0) (j : ℕ) : Measure ℝ := gaussianReal 0 (d j)

def spinSampleTest (b : ℝ) (φ : ℝ → ℝ≥0∞) (z : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, φ x ∂gaussianReal (z/b) (Real.toNNReal (1/b))

def GaussianHierarchyStatement : Prop :=
  ∀ (ms : List ℝ), ms.Pairwise (· < ·) → (∀ m ∈ ms, 0 < m ∧ m < 1) →
  ∀ (d : ℕ → ℝ≥0) (b : ℝ), spinI ms d < b →
    FamilyMomentsFinite ms (spinIncrementLaw d) (spinTerminal b) ∧
    (∀ z, familyRecursion ms (spinIncrementLaw d) (spinTerminal b) z =
      spinC ms d b + z^2/(2*spinLambda ms d b)) ∧
    (∀ p₀ : ℝ≥0,
      (∫ z, ∫ ω, familyLogPartition ms (spinTerminal b) z ω
        ∂familyCascadeLaw ms.length (spinIncrementLaw d) ∂gaussianReal 0 p₀) =
        spinC ms d b + (p₀:ℝ)/(2*spinLambda ms d b)) ∧
    (∀ (p₀ : ℝ≥0) (φ : ℝ → ℝ≥0∞), Measurable φ → (∀ x, φ x ≤ 1) →
      (∫⁻ z, ∫⁻ ω, familyPathGibbs ms (spinTerminal b) (spinSampleTest b φ) z ω
        ∂familyCascadeLaw ms.length (spinIncrementLaw d) ∂gaussianReal 0 p₀) =
      ∫⁻ x, φ x ∂gaussianReal 0
        (Real.toNNReal ((p₀:ℝ)/(spinLambda ms d b)^2 + spinV ms d b + 1/b)))
end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming

def vectorSpinTerminal (N : ℕ) (b : ℝ) (z : Fin N → ℝ) : ℝ :=
  ∑ i, spinTerminal b (z i)

def vectorSpinLaw (N : ℕ) (d : ℕ → ℝ≥0) (j : ℕ) : Measure (Fin N → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 (d j))

def vectorSpinTest (N : ℕ) (b : ℝ) (φ : (Fin N → ℝ) → ℝ≥0∞) (z : Fin N → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, φ x ∂Measure.pi (fun i => gaussianReal (z i/b) (Real.toNNReal (1/b)))

def GaussianVectorStatement : Prop :=
  ∀ (N : ℕ) (ms : List ℝ), ms.Pairwise (· < ·) → (∀ m ∈ ms, 0 < m ∧ m < 1) →
  ∀ (d : ℕ → ℝ≥0) (b : ℝ), spinI ms d < b →
    FamilyMomentsFinite ms (vectorSpinLaw N d) (vectorSpinTerminal N b) ∧
    (∀ z, familyRecursion ms (vectorSpinLaw N d) (vectorSpinTerminal N b) z =
      ∑ i, (spinC ms d b + (z i)^2/(2*spinLambda ms d b))) ∧
    (∀ p₀ : ℝ≥0,
      (∫ z, ∫ ω, familyLogPartition ms (vectorSpinTerminal N b) z ω
        ∂familyCascadeLaw ms.length (vectorSpinLaw N d)
        ∂Measure.pi (fun _ : Fin N => gaussianReal 0 p₀)) =
          N*(spinC ms d b + (p₀:ℝ)/(2*spinLambda ms d b))) ∧
    (∀ (p₀ : ℝ≥0) (φ : (Fin N → ℝ) → ℝ≥0∞), Measurable φ → (∀ x, φ x ≤ 1) →
      (∫⁻ z, ∫⁻ ω, familyPathGibbs ms (vectorSpinTerminal N b) (vectorSpinTest N b φ) z ω
        ∂familyCascadeLaw ms.length (vectorSpinLaw N d)
        ∂Measure.pi (fun _ : Fin N => gaussianReal 0 p₀)) =
      ∫⁻ x, φ x ∂Measure.pi (fun _ : Fin N => gaussianReal 0
        (Real.toNNReal ((p₀:ℝ)/(spinLambda ms d b)^2 + spinV ms d b + 1/b))))
end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MicroscopicJamming

def spinTotalIncrement : List ℝ → (ℕ → ℝ≥0) → ℝ
  | [], _ => 0
  | _::ms, d => (d 0:ℝ) + spinTotalIncrement ms (fun j => d (j+1))

def spinX (ms : List ℝ) (d : ℕ → ℝ≥0) (p₀ : ℝ≥0) (b : ℝ) : ℝ :=
  spinC ms d b + (p₀:ℝ)/(2*spinLambda ms d b)

def spinSaddleLHS (ms : List ℝ) (d : ℕ → ℝ≥0) (p₀ : ℝ≥0) (b : ℝ) : ℝ :=
  1/b + (p₀:ℝ)/(spinLambda ms d b)^2 + spinV ms d b

def SpinSaddleStatement : Prop :=
  ∀ ms : List ℝ, ms.Pairwise (· < ·) → (∀ m ∈ ms, 0 < m ∧ m < 1) →
  ∀ (d : ℕ → ℝ≥0) (p₀ : ℝ≥0),
    (∀ b : ℝ, spinI ms d < b →
      HasDerivAt (spinX ms d p₀) (-(1/2)*spinSaddleLHS ms d p₀ b) b) ∧
    (∃! b : ℝ, spinI ms d < b ∧ spinSaddleLHS ms d p₀ b = 1) ∧
    (∀ b B : ℝ, spinI ms d < b → spinSaddleLHS ms d p₀ b = 1 →
      (p₀:ℝ)+spinTotalIncrement ms d ≤ B → 1 ≤ b ∧ b < 2*(B+1))
end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace MicroscopicJamming

def spinShellBad (N : ℕ) (δ : ℝ) : Set (Fin N → ℝ) :=
  {x | δ < |(∑ i, (x i)^2)/(N:ℝ)-1|}

def gaussianSpinDisorder (N : ℕ) (ms : List ℝ) (d : ℕ → ℝ≥0) (p₀ : ℝ≥0) :
    Measure ((Fin N → ℝ) × FamilyCascadeTree (Fin N → ℝ) ms.length) :=
  (Measure.pi (fun _ : Fin N => gaussianReal 0 p₀)).prod
    (familyCascadeLaw ms.length (vectorSpinLaw N d))

def gaussianSpinBadMass (N : ℕ) (ms : List ℝ) (b δ : ℝ)
    (ω : (Fin N → ℝ) × FamilyCascadeTree (Fin N → ℝ) ms.length) : ℝ≥0∞ :=
  familyPathGibbs ms (vectorSpinTerminal N b)
    (vectorSpinTest N b ((spinShellBad N δ).indicator (fun _ => 1))) ω.1 ω.2

def GaussianShellStatement : Prop :=
  ∀ ms : List ℝ, ms.Pairwise (· < ·) → (∀ m ∈ ms, 0 < m ∧ m < 1) →
  ∀ (d : ℕ → ℝ≥0) (p₀ : ℝ≥0) (b : ℝ), spinI ms d < b →
    spinSaddleLHS ms d p₀ b = 1 →
  ∀ δ : ℝ, 0 < δ →
    Tendsto (fun N => ∫⁻ ω, gaussianSpinBadMass N ms b δ ω ∂gaussianSpinDisorder N ms d p₀)
      atTop (𝓝 0) ∧
    (∀ ε : ℝ, 0 < ε →
      Tendsto (fun N => (gaussianSpinDisorder N ms d p₀)
        {ω | ENNReal.ofReal ε ≤ gaussianSpinBadMass N ms b δ ω}) atTop (𝓝 0))
end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming

def gaussianSpinLog (N : ℕ) (ms : List ℝ) (b : ℝ)
    (ω : (Fin N → ℝ) × FamilyCascadeTree (Fin N → ℝ) ms.length) : ℝ :=
  familyLogPartition ms (vectorSpinTerminal N b) ω.1 ω.2

def GaussianLogMomentStatement : Prop :=
  ∀ ms : List ℝ, ms.Pairwise (· < ·) → (∀ m ∈ ms, 0 < m ∧ m < 1) →
  ∀ (d : ℕ → ℝ≥0) (p₀ : ℝ≥0) (b : ℝ), spinI ms d < b →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 0 < N →
      MemLp (gaussianSpinLog N ms b) 2 (gaussianSpinDisorder N ms d p₀) ∧
      (∫ ω, (gaussianSpinLog N ms b ω)^2 ∂gaussianSpinDisorder N ms d p₀) ≤ C*(N:ℝ)^2
end MicroscopicJamming

 
 
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming
variable {E : Type} [MeasurableSpace E] [Add E] [MeasurableAdd₂ E]

def forgetFamilyMarks : (k : ℕ) → FamilyCascadeTree E k → CascadeTree k
  | 0, _ => ()
  | k+1, ω => mapPointCloud (fun z => forgetFamilyMarks k z.2) ω

def familyUnmarkedTotal (ms : List ℝ) (ω : FamilyCascadeTree E ms.length) : ℝ≥0∞ :=
  cascadeTotal ms (forgetFamilyMarks ms.length ω)

omit [Add E] [MeasurableAdd₂ E] in
lemma measurable_forgetFamilyMarks [Add E] [MeasurableAdd₂ E] (k : ℕ) :
    Measurable (forgetFamilyMarks (E := E) k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih => exact measurable_mapPointCloud (ih.comp measurable_snd)

lemma familyCascadeLaw_forget (ms : List ℝ) (ν : ℕ → Measure E)
    (hν : ∀ j, IsProbabilityMeasure (ν j)) :
    (familyCascadeLaw ms.length ν).map (forgetFamilyMarks ms.length) = cascadeLaw ms := by
  induction ms generalizing ν with
  | nil => exact Measure.map_dirac' measurable_const ()
  | cons m ms ih =>
    let := hν 0
    let := familyCascadeLaw_probability ms.length (fun j => ν (j+1)) (fun j => hν (j+1))
    change (pointCloudLaw ((ν 0).prod (familyCascadeLaw ms.length (fun j => ν (j+1))))).map
      (mapPointCloud (fun z => forgetFamilyMarks ms.length z.2)) = pointCloudLaw (cascadeLaw ms)
    rw [pointCloudLaw_map _ (f := fun z : E × FamilyCascadeTree E ms.length =>
      forgetFamilyMarks ms.length z.2) ((measurable_forgetFamilyMarks ms.length).comp measurable_snd)]
    congr 1
    erw [← Measure.map_map (measurable_forgetFamilyMarks ms.length) measurable_snd,
      Measure.map_snd_prod, measure_univ, one_smul, ih]
    exact fun j => hν (j+1)

lemma measurable_familyLeafTotal (ms : List ℝ) {u : E → ℝ} (hu : Measurable u) :
    Measurable (fun z : E × FamilyCascadeTree E ms.length => familyLeafTotal ms u z.1 z.2) := by
  induction ms with
  | nil => exact (Real.measurable_exp.comp (hu.comp measurable_fst)).ennreal_ofReal
  | cons m ms ih =>
    exact measurable_pointCloudFunctional_param (f := fun z : E × (ℝ × (E × FamilyCascadeTree E ms.length)) =>
      ENNReal.ofReal (z.2.1^(-1/m))*familyLeafTotal ms u (z.1+z.2.2.1) z.2.2.2) ( (by fun_prop : Measurable (fun z : E × (ℝ × (E × FamilyCascadeTree E ms.length)) =>
      ENNReal.ofReal (z.2.1^(-1/m)))).mul
      (ih.comp (by fun_prop : Measurable (fun z : E × (ℝ × (E × FamilyCascadeTree E ms.length)) =>
        (z.1+z.2.2.1,z.2.2.2)))))

lemma measurable_familyUnmarkedTotal (ms : List ℝ) : Measurable (familyUnmarkedTotal (E := E) ms) :=
  (measurable_cascadeTotal ms).comp (measurable_forgetFamilyMarks ms.length)

omit [MeasurableSpace E] [Add E] [MeasurableAdd₂ E] in
lemma familyUnmarkedTotal_cons [MeasurableSpace E] [Add E] [MeasurableAdd₂ E]
    (m : ℝ) (ms : List ℝ) (ω : FamilyCascadeTree E (m::ms).length) :
    familyUnmarkedTotal (m::ms) ω = pointCloudFunctional
      (fun z : ℝ × (E × FamilyCascadeTree E ms.length) =>
        ENNReal.ofReal (z.1^(-1/m))*familyUnmarkedTotal ms z.2.2) ω := rfl

lemma familyUnmarkedTotal_properties (ms : List ℝ) (hms : ms.Pairwise (· < ·))
    (h01 : ∀ m ∈ ms, 0 < m ∧ m < 1) (ν : ℕ → Measure E)
    (hν : ∀ j, IsProbabilityMeasure (ν j)) :
    (∀ᵐ ω ∂familyCascadeLaw ms.length ν,
      0 < familyUnmarkedTotal ms ω ∧ familyUnmarkedTotal ms ω < ∞) ∧
    (∀ a : ℝ, 0 < a → (∀ m ∈ ms, a < m) → Integrable
      (fun ω => (familyUnmarkedTotal ms ω).toReal^a) (familyCascadeLaw ms.length ν)) ∧
    Integrable (fun ω => |Real.log (familyUnmarkedTotal ms ω).toReal|^2)
      (familyCascadeLaw ms.length ν) := by
  have hp : MeasurePreserving (forgetFamilyMarks ms.length) (familyCascadeLaw ms.length ν)
      (cascadeLaw ms) := ⟨measurable_forgetFamilyMarks _, familyCascadeLaw_forget ms ν hν⟩
  have h := cascadeTotal_properties ms hms h01
  exact ⟨hp.quasiMeasurePreserving.ae h.1, fun a ha ham => hp.integrable_comp_of_integrable (h.2.1 a ha ham),
    hp.integrable_comp_of_integrable h.2.2⟩
end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace MicroscopicJamming

def familyPositiveTotal {E : Type} [MeasurableSpace E] [Add E] :
    (ms : List ℝ) → (E → ℝ≥0∞) → E → FamilyCascadeTree E ms.length → ℝ≥0∞
  | [], f, x, _ => f x
  | m::ms, f, x, ω => pointCloudFunctional (fun z : ℝ × (E × FamilyCascadeTree E ms.length) =>
      ENNReal.ofReal (z.1^(-1/m))*familyPositiveTotal ms f (x+z.2.1) z.2.2) ω

def gaussianSpinShellTerminal (N : ℕ) (b δ : ℝ) (z : Fin N → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (vectorSpinTerminal N b z)) *
    vectorSpinTest N b ((spinShellBad N δ)ᶜ.indicator (fun _ => 1)) z

def gaussianSpinShellPartition (N : ℕ) (ms : List ℝ) (b δ : ℝ)
    (ω : (Fin N → ℝ) × FamilyCascadeTree (Fin N → ℝ) ms.length) : ℝ≥0∞ :=
  familyPositiveTotal ms (gaussianSpinShellTerminal N b δ) ω.1 ω.2 /
    familyUnmarkedTotal ms ω.2

def gaussianSpinShellLog (N : ℕ) (ms : List ℝ) (b δ : ℝ)
    (ω : (Fin N → ℝ) × FamilyCascadeTree (Fin N → ℝ) ms.length) : ℝ :=
  Real.log (gaussianSpinShellPartition N ms b δ ω).toReal

def GaussianShellLogStatement : Prop :=
  ∀ ms : List ℝ, ms.Pairwise (· < ·) → (∀ m ∈ ms, 0 < m ∧ m < 1) →
  ∀ (d : ℕ → ℝ≥0) (p₀ : ℝ≥0) (b : ℝ), spinI ms d < b →
    spinSaddleLHS ms d p₀ b = 1 → ∀ δ : ℝ, 0 < δ → δ < 1 →
    (∀ N : ℕ, 0 < N → Integrable (gaussianSpinShellLog N ms b δ) (gaussianSpinDisorder N ms d p₀)) ∧
    Tendsto (fun N : ℕ => (∫ ω, gaussianSpinShellLog N ms b δ ω
      ∂gaussianSpinDisorder N ms d p₀)/(N:ℝ)) atTop
      (𝓝 (spinC ms d b+(p₀:ℝ)/(2*spinLambda ms d b)))
end MicroscopicJamming

end

end OAI
