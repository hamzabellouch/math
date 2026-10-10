import OAI.Probability.ContinuumTransition.CompactHulls

namespace OAI

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

def triangleDet (w : Fin 3 → Parameter) : ℝ :=
  ((w 1).1-(w 0).1)*((w 2).2-(w 0).2)-((w 1).2-(w 0).2)*((w 2).1-(w 0).1)

def triangleWeight (w : Fin 3 → Parameter) (z : Parameter) (i : Fin 3) : ℝ :=
  let b := ((z.1-(w 0).1)*((w 2).2-(w 0).2)-(z.2-(w 0).2)*((w 2).1-(w 0).1))/triangleDet w
  let c := (((w 1).1-(w 0).1)*(z.2-(w 0).2)-((w 1).2-(w 0).2)*(z.1-(w 0).1))/triangleDet w
  if i = 0 then 1-b-c else if i = 1 then b else c

lemma triangleWeight_sum (w : Fin 3 → Parameter) (z : Parameter) :
    ∑ i, triangleWeight w z i = 1 := by
  simp [Fin.sum_univ_succ,triangleWeight]

lemma triangleWeight_combination {w : Fin 3 → Parameter} (hD : triangleDet w ≠ 0)
    (z : Parameter) : ∑ i, triangleWeight w z i • w i = z := by
  ext
  all_goals
    simp only [Prod.fst_sum,Prod.snd_sum,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
    simp [Fin.sum_univ_succ,triangleWeight]
    field_simp
    dsimp [triangleDet] at hD ⊢
    field_simp at *
    ring

lemma triangle_mem_of_weights {w : Fin 3 → Parameter} (hD : triangleDet w ≠ 0)
    {z : Parameter} (hz : ∀ i, 0 ≤ triangleWeight w z i) : z ∈ convexHull ℝ (range w) := by
  rw [← triangleWeight_combination hD z]
  exact (convex_convexHull ℝ (range w)).sum_mem (fun i _ => hz i)
    (triangleWeight_sum w z) (fun i _ => subset_convexHull ℝ _ (mem_range_self i))

def triangleVertex (p : ℝ) (i : Fin 3) : Parameter := if i = 0 then (0,0) else if i = 1 then (3*p/4,p) else (12*p,4*p)
def triangleCenter (p : ℝ) : Parameter := (17*p/4,5*p/3)

lemma triangleDet_vertex {p : ℝ} (hp : 0 < p) : triangleDet (triangleVertex p) ≠ 0 := by
  have he : triangleDet (triangleVertex p) = -9*p^2 := by norm_num [triangleDet,triangleVertex,show (2:Fin 3) ≠ 0 by decide,show (2:Fin 3) ≠ 1 by decide]; ring
  rw [he]
  exact mul_ne_zero (by norm_num) (pow_ne_zero _ hp.ne')

lemma triangleWeight_center {p : ℝ} (hp : 0 < p) (i : Fin 3) :
    triangleWeight (triangleVertex p) (triangleCenter p) i = 1/3 := by
  fin_cases i <;> norm_num [triangleWeight,triangleVertex,triangleCenter,triangleDet,show (2:Fin 3) ≠ 0 by decide,show (2:Fin 3) ≠ 1 by decide]
  all_goals field_simp [hp.ne']; ring

lemma continuous_triangleDet : Continuous triangleDet := by unfold triangleDet; fun_prop

lemma continuousAt_triangleWeight {w : Fin 3 → Parameter} {z : Parameter}
    (hD : triangleDet w ≠ 0) (i : Fin 3) :
    ContinuousAt (fun q : (Fin 3 → Parameter) × Parameter => triangleWeight q.1 q.2 i) (w,z) := by
  have hc := continuous_triangleDet
  unfold triangleWeight
  split_ifs <;> fun_prop (disch := exact hD)

lemma robust_vertex_triangle {p : ℝ} (hp : 0 < p) :
    ∃ τ γ : ℝ, 0 < τ ∧ 0 < γ ∧
      ∀ w : Fin 3 → Parameter, (∀ i, dist (w i) (triangleVertex p i) ≤ τ) →
        closedBall (triangleCenter p) γ ⊆ convexHull ℝ (range w) := by
  let v := triangleVertex p
  let g := triangleCenter p
  have hD : triangleDet v ≠ 0 := triangleDet_vertex hp
  have hne : ∀ᶠ q : (Fin 3 → Parameter) × Parameter in 𝓝 (v,g), triangleDet q.1 ≠ 0 :=
    (continuous_triangleDet.continuousAt.comp continuousAt_fst).eventually_ne hD
  have hpos : ∀ᶠ q : (Fin 3 → Parameter) × Parameter in 𝓝 (v,g), ∀ i, 0 < triangleWeight q.1 q.2 i := by
    apply Filter.eventually_all.mpr
    intro i
    exact (continuousAt_triangleWeight (z := g) hD i).eventually (Ioi_mem_nhds (by change 0 < triangleWeight (triangleVertex p) (triangleCenter p) i; rw [triangleWeight_center hp]; norm_num))
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp (hne.and hpos)
  refine ⟨δ/2,δ/2,by positivity,by positivity,?_⟩
  intro w hw z hz
  have hd : dist (w,z) (v,g) < δ := by
    rw [Prod.dist_eq,max_lt_iff]
    constructor
    · exact lt_of_le_of_lt ((dist_pi_le_iff (by positivity : 0 ≤ δ/2)).mpr hw) (by linarith)
    · exact lt_of_le_of_lt hz (by linarith)
  have hh := hball hd
  exact triangle_mem_of_weights hh.1 (fun i => (hh.2 i).le)

end ContinuumTemperature
end
end

end OAI
