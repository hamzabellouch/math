import Mathlib
import OAI.GroupTheory.FiniteType.SingularSubdivision

namespace OAI

noncomputable section
open CategoryTheory AlgebraicTopology Limits
open scoped Simplicial
namespace SingularSupport
open CategoryTheory AlgebraicTopology Limits SingularChains
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {n m : ℕ}

abbrev gen (f : C(Std n,X)) : (chains X).X n := generator f 1

def span (P : C(Std n,X) → Prop) : Submodule ℤ ((chains X).X n) :=
  Submodule.span ℤ {x | ∃ f, P f ∧ x = gen f}

lemma gen_mem {P : C(Std n,X) → Prop} (f : C(Std n,X)) (hf : P f) : gen f ∈ span P :=
  Submodule.subset_span ⟨f,hf,rfl⟩

lemma span_mono {P Q : C(Std n,X) → Prop} (h : ∀ f, P f → Q f) : span P ≤ span Q := by
  apply Submodule.span_le.mpr
  rintro _ ⟨f,hf,rfl⟩
  exact gen_mem f (h f hf)

lemma map_mem {P : C(Std n,X) → Prop} {A : ModuleCat ℤ} {S : Submodule ℤ A}
    (g : (chains X).X n ⟶ A) (hg : ∀ f, P f → g (gen f) ∈ S)
    {c : (chains X).X n} (hc : c ∈ span P) : g c ∈ S := by
  induction hc using Submodule.span_induction with
  | mem x hx => obtain ⟨f,hf,rfl⟩ := hx; exact hg f hf
  | zero => simp
  | add x y hx hy ihx ihy => simpa using S.add_mem ihx ihy
  | smul a x hx ih => simpa using S.smul_mem a ih

lemma induction_on (S : Submodule ℤ ((chains X).X n))
    (hS : ∀ f : C(Std n,X), gen f ∈ S) (c : (chains X).X n) : c ∈ S := by
  let : Module ℤ (((chains X).X n) ⧸ S) := Submodule.Quotient.module S
  let q : (chains X).X n ⟶ ModuleCat.of ℤ (((chains X).X n) ⧸ S) := ModuleCat.ofHom S.mkQ
  have hq : q = 0 := by
    apply hom_ext
    intro f
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    change S.mkQ (gen f) = 0
    change gen f ∈ LinearMap.ker S.mkQ
    rw [Submodule.ker_mkQ]
    exact hS f
  have hc := congrArg (fun h => h c) hq
  change S.mkQ c = 0 at hc
  have hc' : c ∈ LinearMap.ker S.mkQ := hc
  simpa only [Submodule.ker_mkQ] using hc'

@[simp] lemma map_gen (f : C(Std n,X)) (g : C(X,Y)) : (map g).f n (gen f) = gen (g.comp f) :=
  congrArg (fun h : ModuleCat.of ℤ ℤ ⟶ (chains Y).X n => h 1) (generator_map f g)

lemma boundary_gen (f : C(Std (n+1),X)) :
    (chains X).d (n+1) n (gen f) = ∑ i : Fin (n+2), (-1:ℤ)^i.val • gen (f.comp (face i)) := by
  have h := congrArg (fun h : ModuleCat.of ℤ ℤ ⟶ (chains X).X n => h 1) (generator_boundary f)
  simpa using h

end SingularSupport

namespace SmallChains
open Set CategoryTheory AlgebraicTopology Limits SingularChains
variable {X : Type} [TopologicalSpace X] {ι : Type} (U : ι → Set X)

abbrev Small {n : ℕ} (f : C(Std n,X)) : Prop := ∃ i, range f ⊆ U i

def group (n : ℕ) : Submodule ℤ ((chains X).X n) := SingularSupport.span (Small U)

lemma small_comp {n m : ℕ} (f : C(Std n,X)) (hf : Small U f) (g : C(Std m,Std n)) :
    Small U (f.comp g) := by
  obtain ⟨i,hi⟩ := hf
  exact ⟨i,by rintro _ ⟨s,rfl⟩; exact hi (mem_range_self _)⟩

lemma gen_mem {n : ℕ} (f : C(Std n,X)) (hf : Small U f) : SingularSupport.gen f ∈ group U n :=
  SingularSupport.gen_mem f hf

lemma boundary_mem {n : ℕ} {c : (chains X).X (n+1)} (hc : c ∈ group U (n+1)) :
    (chains X).d (n+1) n c ∈ group U n := by
  apply SingularSupport.map_mem _ _ hc
  intro f hf
  rw [SingularSupport.boundary_gen]
  apply Submodule.sum_mem
  intro i _
  apply AddSubgroup.zsmul_mem (group U n).toAddSubgroup
  exact gen_mem U _ (small_comp U f hf (face i))

lemma realize_mem {n m : ℕ} (f : C(Std n,X)) (hf : Small U f)
    (c : (AffineChains.chains (Std n)).X m) :
    (map f).f m ((AffineRealization.realize n).f m c) ∈ group U m := by
  let g := (AffineRealization.realize n).f m ≫ (map f).f m
  apply AffineSupport.induction_on ((group U m).comap g.hom) _ c
  intro v
  change (AffineChains.generator v ≫ g) 1 ∈ group U m
  change (AffineChains.generator v ≫ (AffineRealization.realize n).f m ≫ (map f).f m) 1 ∈ group U m
  rw [AffineRealization.generator_realize_assoc,generator_map]
  exact gen_mem U _ (small_comp U f hf (ConvexSimplex.affine v))

lemma subdiv_mem {n : ℕ} {c : (chains X).X n} (hc : c ∈ group U n) :
    SingularSubdivision.subdiv n c ∈ group U n := by
  apply SingularSupport.map_mem _ _ hc
  intro f hf
  change (generator f ≫ SingularSubdivision.subdiv n) 1 ∈ group U n
  rw [SingularSubdivision.generator_subdiv]
  exact realize_mem U f hf (SingularSubdivision.simplexChain n 1)

lemma prism_mem {n : ℕ} {c : (chains X).X n} (hc : c ∈ group U n) :
    SingularSubdivision.prism n c ∈ group U (n+1) := by
  apply SingularSupport.map_mem _ _ hc
  intro f hf
  change (generator f ≫ SingularSubdivision.prism n) 1 ∈ group U (n+1)
  rw [SingularSubdivision.generator_prism]
  exact realize_mem U f hf (SingularSubdivision.prismChain n 1)

end SmallChains

namespace AffineMesh
open Set Topology
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def center {n : ℕ} (v : Fin (n+1) → E) : E := ((n+1:ℝ)⁻¹) • ∑ i, v i

def ratio (n : ℕ) : ℝ := (n:ℝ)/(n+1)

lemma ratio_nonneg (n : ℕ) : 0 ≤ ratio n := by unfold ratio; positivity
lemma ratio_lt_one (n : ℕ) : ratio n < 1 := by
  unfold ratio
  exact (div_lt_one (by positivity)).mpr (by linarith)
lemma ratio_mono {m n : ℕ} (h : m ≤ n) : ratio m ≤ ratio n := by
  unfold ratio
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have : (m:ℝ) ≤ n := Nat.cast_le.mpr h
  nlinarith

lemma center_mem_hull {n : ℕ} (v : Fin (n+1) → E) : center v ∈ convexHull ℝ (range v) := by
  have he : center v = AffineSimplex.simplex v Convexity.StdSimplex.barycenter := by
    simp [center,AffineSimplex.simplex_apply,
      Convexity.StdSimplex.weights_barycenter_apply,Finset.smul_sum]
  rw [he]
  exact AffineSimplex.simplex_mem_hull _ _

lemma center_sub {n : ℕ} (v : Fin (n+1) → E) (i : Fin (n+1)) :
    center v - v i = ((n+1:ℝ)⁻¹) • ∑ j, (v j - v i) := by
  rw [Finset.sum_sub_distrib,smul_sub]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℝ,smul_smul]
  have h : ((n+1:ℝ)⁻¹) * (n+1) = 1 := inv_mul_cancel₀ (by positivity)
  simp only [Nat.cast_add,Nat.cast_one,h,one_smul]
  rfl

lemma center_dist_vertex {n : ℕ} (v : Fin (n+1) → E) {D : ℝ} (_hD : 0 ≤ D)
    (hv : ∀ i j, dist (v i) (v j) ≤ D) (i : Fin (n+1)) :
    dist (center v) (v i) ≤ ratio n * D := by
  rw [dist_eq_norm,center_sub,norm_smul,Real.norm_of_nonneg (by positivity)]
  have hs : ∑ j : Fin (n+1), ‖v j - v i‖ ≤ (n:ℝ) * D := by
    classical
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    simp only [sub_self,norm_zero,add_zero]
    calc
      _ ≤ ∑ j ∈ Finset.univ.erase i, D := Finset.sum_le_sum (fun j _ => by
        simpa only [dist_eq_norm] using hv j i)
      _ = (n:ℝ) * D := by simp
  calc
    _ ≤ ((n+1:ℝ)⁻¹) * (∑ j, ‖v j - v i‖) :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ ((n+1:ℝ)⁻¹) * ((n:ℝ) * D) := mul_le_mul_of_nonneg_left hs (by positivity)
    _ = ratio n * D := by unfold ratio; ring

lemma center_dist_hull {n : ℕ} (v : Fin (n+1) → E) {D : ℝ} (hD : 0 ≤ D)
    (hv : ∀ i j, dist (v i) (v j) ≤ D) {p : E} (hp : p ∈ convexHull ℝ (range v)) :
    dist (center v) p ≤ ratio n * D := by
  have hc : convexHull ℝ (range v) ⊆ Metric.closedBall (center v) (ratio n * D) := by
    apply convexHull_min _ (convex_closedBall _ _)
    rintro _ ⟨i,rfl⟩
    rw [Metric.mem_closedBall,dist_comm]
    exact center_dist_vertex v hD hv i
  simpa only [Metric.mem_closedBall,dist_comm] using hc hp

lemma hull_dist {n : ℕ} (v : Fin (n+1) → E) {D : ℝ} (_hD : 0 ≤ D)
    (hv : ∀ i j, dist (v i) (v j) ≤ D) {p q : E}
    (hp : p ∈ convexHull ℝ (range v)) (hq : q ∈ convexHull ℝ (range v)) : dist p q ≤ D := by
  have hi : ∀ i, convexHull ℝ (range v) ⊆ Metric.closedBall (v i) D := by
    intro i
    apply convexHull_min _ (convex_closedBall _ _)
    rintro _ ⟨j,rfl⟩
    exact hv j i
  have hc : convexHull ℝ (range v) ⊆ Metric.closedBall q D := by
    apply convexHull_min _ (convex_closedBall _ _)
    rintro _ ⟨i,rfl⟩
    simpa only [Metric.mem_closedBall,dist_comm] using hi i hq
  exact hc hp

end AffineMesh

namespace ConvexSimplex

instance stdMetricSpace (n : ℕ) : MetricSpace (Std n) :=
  Topology.IsEmbedding.comapMetricSpace
    (fun point : Std n => (point.weights : Fin (n+1) → ℝ))
    (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n+1)))

end ConvexSimplex

namespace SubdivisionMesh
section
open Set Topology CategoryTheory ConvexSimplex AffineSupport
variable {N n m : ℕ}

def InHull (v : Fin (n+1) → Std N) (w : Fin (m+1) → Std N) : Prop :=
  ∀ i, ((w i).weights : Fin (N+1) → ℝ) ∈
    convexHull ℝ (range (fun j => ((v j).weights : Fin (N+1) → ℝ)))

def MeshLe (D : ℝ) (v : Fin (n+1) → Std N) : Prop := ∀ i j, dist (v i) (v j) ≤ D

def Good (v : Fin (n+1) → Std N) (D : ℝ) (w : Fin (m+1) → Std N) : Prop :=
  InHull v w ∧ MeshLe D w

lemma hull_self (v : Fin (n+1) → Std N) : InHull v v :=
  fun i => subset_convexHull ℝ _ (mem_range_self i)

lemma hull_face_subset (v : Fin (n+2) → Std N) (i : Fin (n+2)) :
    convexHull ℝ (range (fun j => ((v (i.succAbove j)).weights : Fin (N+1) → ℝ))) ⊆
      convexHull ℝ (range (fun j => ((v j).weights : Fin (N+1) → ℝ))) :=
  convexHull_mono (by rintro _ ⟨j,rfl⟩; exact mem_range_self _)

lemma center_hull (v : Fin (n+1) → Std N) :
    ((center v).weights : Fin (N+1) → ℝ) ∈
      convexHull ℝ (range (fun j => ((v j).weights : Fin (N+1) → ℝ))) := by
  rw [center_coe,Finsupp.coe_smul,Finsupp.coe_finsetSum]
  exact AffineMesh.center_mem_hull _

lemma center_dist_hull (v : Fin (n+1) → Std N) {D : ℝ} (hD : 0 ≤ D) (hv : MeshLe D v)
    {w : Std N} (hw : (w.weights : Fin (N+1) → ℝ) ∈
      convexHull ℝ (range (fun j => ((v j).weights : Fin (N+1) → ℝ)))) :
    dist (center v) w ≤ AffineMesh.ratio n * D := by
  change dist ((center v).weights : Fin (N+1) → ℝ) w.weights ≤ _
  rw [center_coe,Finsupp.coe_smul,Finsupp.coe_finsetSum]
  exact AffineMesh.center_dist_hull (fun vertex => ((v vertex).weights : Fin (N+1) → ℝ))
    hD (fun first second => hv first second) hw

lemma good_cone (v : Fin (n+2) → Std N) (i : Fin (n+2)) {D : ℝ} (hD : 0 ≤ D)
    (hv : MeshLe D v) (w : Fin (n+1) → Std N)
    (hw : Good (v ∘ i.succAbove) (AffineMesh.ratio n * D) w) :
    Good v (AffineMesh.ratio (n+1) * D) (Fin.cons (center v) w) := by
  constructor
  · intro j
    induction j using Fin.cases with
    | zero => exact center_hull v
    | succ j => exact hull_face_subset v i (hw.1 j)
  · intro j k
    induction j using Fin.cases with
    | zero =>
      induction k using Fin.cases with
      | zero => simpa using mul_nonneg (AffineMesh.ratio_nonneg (n+1)) hD
      | succ k => exact center_dist_hull v hD hv (hull_face_subset v i (hw.1 k))
    | succ j =>
      induction k using Fin.cases with
      | zero => simpa only [Fin.cons_succ,Fin.cons_zero,dist_comm] using
          center_dist_hull v hD hv (hull_face_subset v i (hw.1 j))
      | succ k => exact (hw.2 j k).trans (mul_le_mul_of_nonneg_right
          (AffineMesh.ratio_mono (Nat.le_succ n)) hD)

theorem subdiv_mesh (n : ℕ) (v : Fin (n+1) → Std N) {D : ℝ} (hD : 0 ≤ D) (hv : MeshLe D v) :
    AffineChains.subdiv (@center N) n (gen v) ∈ span (Good v (AffineMesh.ratio n * D)) := by
  induction n with
  | zero =>
    rw [AffineChains.subdiv_zero]
    apply gen_mem
    constructor
    · exact hull_self v
    · intro i j
      have hij : i = j := by omega
      simp [hij,AffineMesh.ratio]
  | succ n ih =>
    rw [subdiv_gen]
    apply Submodule.sum_mem
    intro i _
    apply AddSubgroup.zsmul_mem (span (Good v (AffineMesh.ratio (n+1) * D))).toAddSubgroup
    apply map_mem (P := Good (v ∘ i.succAbove) (AffineMesh.ratio n * D))
      (AffineChains.cone (center v) n)
    · intro w hw
      rw [cone_gen]
      exact gen_mem _ (good_cone v i hD hv w hw)
    · exact ih (v ∘ i.succAbove) (fun j k => hv _ _)

end

open Set Topology CategoryTheory ConvexSimplex AffineSupport
variable {N n : ℕ}

def iterate (N n k : ℕ) : (AffineChains.chains (Std N)).X n ⟶ (AffineChains.chains (Std N)).X n :=
  match k with
  | 0 => 𝟙 _
  | k+1 => iterate N n k ≫ AffineChains.subdiv (@center N) n

lemma subdiv_mem {D : ℝ} (hD : 0 ≤ D) {c : (AffineChains.chains (Std N)).X n}
    (hc : c ∈ span (MeshLe D)) :
    AffineChains.subdiv (@center N) n c ∈ span (MeshLe (AffineMesh.ratio n * D)) := by
  apply map_mem _ _ hc
  intro v hv
  exact span_mono (fun _ h => h.2) (subdiv_mesh n v hD hv)

lemma iterate_mesh {D : ℝ} (hD : 0 ≤ D) {c : (AffineChains.chains (Std N)).X n}
    (hc : c ∈ span (MeshLe D)) (k : ℕ) :
    iterate N n k c ∈ span (MeshLe (AffineMesh.ratio n ^ k * D)) := by
  induction k with
  | zero => simpa [iterate] using hc
  | succ k ih =>
    have h := subdiv_mem (mul_nonneg (pow_nonneg (AffineMesh.ratio_nonneg _) _) hD) ih
    simpa [iterate,pow_succ,mul_assoc,mul_left_comm,mul_comm] using h

lemma basis_mesh (n : ℕ) : MeshLe 2 (AffineRealization.basis n) := by
  intro i j
  change dist ((AffineRealization.basis n i).weights : Fin (n+1) → ℝ)
    (AffineRealization.basis n j).weights ≤ 2
  apply (Metric.dist_le_diam_of_mem
    (Convexity.StdSimplex.isBounded_range_toFun_comp_weights (Fin (n+1)))
    (mem_range_self (AffineRealization.basis n i))
    (mem_range_self (AffineRealization.basis n j))).trans
  exact (Convexity.StdSimplex.diam_range_toFun_comp_weights_subset_closedBall
    (Fin (n+1))).trans (by norm_num)

end SubdivisionMesh

end

end OAI
