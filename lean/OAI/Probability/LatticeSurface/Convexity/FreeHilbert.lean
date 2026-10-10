import Mathlib
import OAI.Probability.LatticeSurface.Dynamics.ProjectionExistence
import OAI.Probability.LatticeSurface.Skorokhod.SkorokhodSupport

namespace OAI

namespace ConvexSkorokhod

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma project_norm_min (B : Body E) (v q : E) (hq : q∈B.carrier) :
    ‖project B v-v‖ ≤ ‖q-v‖ := by
  have hi := project_variational B v q hq
  have he : q-v=(q-project B v)+(project B v-v) := by abel
  have hs := norm_add_sq_real (q-project B v) (project B v-v)
  rw [← he,real_inner_comm (project B v-v) (q-project B v)] at hs
  nlinarith [sq_nonneg ‖q-project B v‖,norm_nonneg (q-v),norm_nonneg (project B v-v)]

end ConvexSkorokhod

noncomputable section

namespace ProjectionComparison

open Set

attribute [local instance] Classical.propDecidable

variable {V E : Type*} [Fintype V]

abbrev FreeSpace (S : System V E) := EuclideanSpace ℝ {x // x∉S.pins}

def freeCoordinates (S : System V E) (h : V → ℝ) : FreeSpace S := WithLp.toLp 2 (fun x => h x)

def extendFree (S : System V E) (b : V → ℝ) (u : FreeSpace S) (x : V) : ℝ :=
  if hx : x∈S.pins then b x else u ⟨x,hx⟩

def freeCarrier (S : System V E) (b : V → ℝ) : Set (FreeSpace S) :=
  {u | extendFree S b u∈feasible S b}

end ProjectionComparison

namespace ProjectionComparison

open Set

attribute [local instance] Classical.propDecidable

variable {V E : Type*} [Fintype V]

omit [Fintype V] in
lemma extendFree_coordinates (S : System V E) (b h : V → ℝ) (hh : ∀x∈S.pins,h x=b x) :
    extendFree S b (freeCoordinates S h)=h := by
  funext x
  by_cases hx : x∈S.pins
  · simp [extendFree,hx,hh x hx]
  · simp [extendFree,hx,freeCoordinates]

omit [Fintype V] in
lemma extendFree_continuous (S : System V E) (b : V → ℝ) : Continuous (extendFree S b) := by
  apply continuous_pi
  intro x
  by_cases hx : x∈S.pins
  · simpa only [extendFree,dite_eq_left hx] using (continuous_const : Continuous (fun _ : FreeSpace S => b x))
  · simpa only [extendFree,dite_eq_right hx] using (PiLp.continuous_apply 2 (fun _ : {x // x∉S.pins} => ℝ) ⟨x,hx⟩)

omit [Fintype V] in
lemma extendFree_combo (S : System V E) (b : V → ℝ) (u v : FreeSpace S) (a d : ℝ) (ha : a+d=1) :
    extendFree S b (a • u+d • v)=fun x => a*extendFree S b u x+d*extendFree S b v x := by
  funext x
  by_cases hx : x∈S.pins
  · simp only [extendFree,dite_eq_left hx]
    rw [← add_mul,ha,one_mul]
  · simp [extendFree,hx,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]

omit [Fintype V] in
lemma freeCarrier_closed (S : System V E) (b : V → ℝ) : IsClosed (freeCarrier S b) :=
  (isClosed_feasible S b).preimage (extendFree_continuous S b)

omit [Fintype V] in
lemma freeCarrier_convex (S : System V E) (b : V → ℝ) : Convex ℝ (freeCarrier S b) := by
  intro u hu v hv a d ha hd had
  change extendFree S b (a • u+d • v)∈feasible S b
  rw [extendFree_combo S b u v a d had]
  refine ⟨fun e => ?_,fun x hx => ?_⟩
  · have h₀ := mul_le_mul_of_nonneg_left (hu.1 e) ha
    have h₁ := mul_le_mul_of_nonneg_left (hv.1 e) hd
    dsimp only
    have he : a*S.cost e+d*S.cost e=S.cost e := by rw [← add_mul,had,one_mul]
    linarith
  · dsimp only
    rw [hu.2 x hx,hv.2 x hx,← add_mul,had,one_mul]

lemma objective_free (S : System V E) (b v : V → ℝ) (u : FreeSpace S) :
    objective v (extendFree S b u)=
      (∑x:{x // x∈S.pins},(b x-v x)^2)+‖u-freeCoordinates S v‖^2 := by
  unfold objective
  rw [← Fintype.sum_subtype_add_sum_subtype (fun x => x∈S.pins),EuclideanSpace.real_norm_sq_eq]
  congr 1
  · apply Finset.sum_congr rfl
    intro x hx
    simp [extendFree,x.property]
  · apply Finset.sum_congr rfl
    intro x hx
    simp [extendFree,x.property,freeCoordinates]

end ProjectionComparison

namespace ProjectionComparison

open Set

attribute [local instance] Classical.propDecidable

variable {V E : Type*} [Fintype V]

theorem exists_free_body (S : System V E) (b : V → ℝ) (hne : (feasible S b).Nonempty) :
    ∃ B : ConvexSkorokhod.Body (FreeSpace S),B.carrier=freeCarrier S b ∧
      ∀v:V → ℝ,extendFree S b (ConvexSkorokhod.project B (freeCoordinates S v))=project S b hne v := by
  have hfree : (freeCarrier S b).Nonempty := by
    obtain ⟨h,hh⟩ := hne
    refine ⟨freeCoordinates S h,?_⟩
    change extendFree S b (freeCoordinates S h)∈feasible S b
    rwa [extendFree_coordinates S b h hh.2]
  let B : ConvexSkorokhod.Body (FreeSpace S) :=
    ⟨freeCarrier S b,hfree,freeCarrier_closed S b,freeCarrier_convex S b⟩
  refine ⟨B,rfl,fun v => ?_⟩
  apply projection_unique S b v _ _ ?_ (project_spec S b hne v)
  refine ⟨ConvexSkorokhod.project_mem B _,fun h hh => ?_⟩
  have hc : freeCoordinates S h∈B.carrier := by
    change extendFree S b (freeCoordinates S h)∈feasible S b
    rwa [extendFree_coordinates S b h hh.2]
  have hdist := ConvexSkorokhod.project_norm_min B (freeCoordinates S v) (freeCoordinates S h) hc
  rw [← extendFree_coordinates S b h hh.2,objective_free,objective_free]
  gcongr

end ProjectionComparison

end

end OAI
