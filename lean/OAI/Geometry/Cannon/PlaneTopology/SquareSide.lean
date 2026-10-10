import Mathlib
import OAI.Geometry.Cannon.Boundary.BoundaryUniformEmbeddedGraph
import OAI.Geometry.Cannon.PlaneTopology.HomeoPlane
import OAI.Geometry.Cannon.Topology.Glue

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
namespace CannonRegularDisk
open Metric
open unitInterval

variable {X : Type*} [TopologicalSpace X]

def squareSide : Fin 4 → Set (I×I) :=
  ![{z | z.1=0},{z | z.1=1},{z | z.2=0},{z | z.2=1}]

def squareBoundary : Set (I×I) := ⋃ i, squareSide i

lemma squareSide_closed (i : Fin 4) : IsClosed (squareSide i) := by
  fin_cases i <;> dsimp [squareSide] <;> exact isClosed_eq (by fun_prop) continuous_const

lemma squareBoundary_closed : IsClosed squareBoundary :=
  isClosed_iUnion_of_finite squareSide_closed

lemma mem_squareBoundary (z : I×I) :
    z∈squareBoundary ↔ z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1 := by
  simp [squareBoundary,squareSide,Fin.exists_fin_succ]

theorem square_boundary_map (a b c d : C(I,X))
    (h₀₀ : a 0=c 0) (h₀₁ : a 1=d 0) (h₁₀ : b 0=c 1) (h₁₁ : b 1=d 1) :
    ∃ f : C(squareBoundary,X),
      (∀ t, f ⟨(0,t),mem_squareBoundary _ |>.mpr (Or.inl rfl)⟩=a t) ∧
      (∀ t, f ⟨(1,t),mem_squareBoundary _ |>.mpr (Or.inr (Or.inl rfl))⟩=b t) ∧
      (∀ s, f ⟨(s,0),mem_squareBoundary _ |>.mpr (Or.inr (Or.inr (Or.inl rfl)))⟩=c s) ∧
      (∀ s, f ⟨(s,1),mem_squareBoundary _ |>.mpr (Or.inr (Or.inr (Or.inr rfl)))⟩=d s) := by
  classical
  let S (i : Fin 4) : Set squareBoundary := Subtype.val ⁻¹' squareSide i
  have hS (i : Fin 4) : IsClosed (S i) := (squareSide_closed i).preimage continuous_subtype_val
  have hc : ⋃ i, S i=univ := by
    ext z
    simp only [mem_iUnion,mem_univ,iff_true]
    exact (mem_iUnion.mp z.property : ∃ i, z.val∈squareSide i)
  let g : Fin 4 → C(I×I,X) :=
    ![a.comp ⟨Prod.snd,continuous_snd⟩,b.comp ⟨Prod.snd,continuous_snd⟩,
      c.comp ⟨Prod.fst,continuous_fst⟩,d.comp ⟨Prod.fst,continuous_fst⟩]
  let f (i : Fin 4) : C(S i,X) :=
    (g i).comp ⟨fun z => z.val.val,continuous_subtype_val.comp continuous_subtype_val⟩
  have heq (i j : Fin 4) (z : squareBoundary) (hi : z∈S i) (hj : z∈S j) :
      f i ⟨z,hi⟩=f j ⟨z,hj⟩ := by
    fin_cases i <;> fin_cases j <;>
      simp only [S,squareSide,Matrix.cons_val_zero,Matrix.cons_val_one,
        Fin.isValue,Fin.reduceFinMk,mem_preimage,mem_ofPred_eq] at hi hj <;>
      simp [f,g,hi,hj] <;> simp_all
  let F := CannonClosedGluing.glue S hS hc f heq
  have hF (i : Fin 4) (z : squareBoundary) (hz : z∈S i) : F z=g i z.val := by
    exact CannonClosedGluing.glue_apply S hS hc f heq i ⟨z,hz⟩
  refine ⟨F,fun t => hF 0 _ rfl,fun t => hF 1 _ rfl,
    fun s => hF 2 _ rfl,fun s => hF 3 _ rfl⟩

theorem IsRegularDisk.fill_square {U : Set X} (hU : IsRegularDisk U)
    (a b c d : C(I,X))
    (h₀₀ : a 0=c 0) (h₀₁ : a 1=d 0) (h₁₀ : b 0=c 1) (h₁₁ : b 1=d 1)
    (ha : range a⊆U) (hb : range b⊆U) (hc : range c⊆U) (hd : range d⊆U) :
    ∃ F : C(I×I,X), (∀ z, F z∈U) ∧
      (∀ t, F (0,t)=a t) ∧ (∀ t, F (1,t)=b t) ∧
      (∀ s, F (s,0)=c s) ∧ (∀ s, F (s,1)=d s) := by
  obtain ⟨f,hfa,hfb,hfc,hfd⟩ := square_boundary_map a b c d h₀₀ h₀₁ h₁₀ h₁₁
  have hf (z : squareBoundary) : f z∈U := by
    have hz (v : I×I) (hv : v∈squareBoundary) (h : z.val=v) : z=⟨v,hv⟩ := Subtype.ext h
    rcases (mem_squareBoundary z.val).mp z.property with h|h|h|h
    · have he := hz (0,z.val.2) (by simp [mem_squareBoundary]) (Prod.ext h rfl)
      rw [he,hfa]; exact ha (mem_range_self _)
    · have he := hz (1,z.val.2) (by simp [mem_squareBoundary]) (Prod.ext h rfl)
      rw [he,hfb]; exact hb (mem_range_self _)
    · have he := hz (z.val.1,0) (by simp [mem_squareBoundary]) (Prod.ext rfl h)
      rw [he,hfc]; exact hc (mem_range_self _)
    · have he := hz (z.val.1,1) (by simp [mem_squareBoundary]) (Prod.ext rfl h)
      rw [he,hfd]; exact hd (mem_range_self _)
  obtain ⟨F,hFU,hF⟩ := hU.extend squareBoundary_closed f hf
  have hFe (z : squareBoundary) : F z.val=f z := congrArg (fun f : C(squareBoundary,X) => f z) hF
  exact ⟨F,hFU,fun t => (hFe _).trans (hfa t),fun t => (hFe _).trans (hfb t),
    fun s => (hFe _).trans (hfc s),fun s => (hFe _).trans (hfd s)⟩

end CannonRegularDisk

namespace CannonGrid
open Set Metric Topology unitInterval

variable {X : Type*} [TopologicalSpace X]

def point (n : ℕ) (hn : 0<n) (i : Fin (n+1)) : I :=
  ⟨(i:ℝ)/n,div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _),
    (div_le_one (by exact_mod_cast hn)).mpr (by exact_mod_cast Nat.le_of_lt_succ i.isLt)⟩

def strip (n : ℕ) (i : Fin n) : Set (I×I) :=
  {z | (i:ℝ)≤n*(z.2:ℝ) ∧ n*(z.2:ℝ)≤(i:ℝ)+1}

lemma strip_closed (n : ℕ) (i : Fin n) : IsClosed (strip n i) := by
  change IsClosed ({z : I×I | (i:ℝ)≤n*(z.2:ℝ)} ∩ {z : I×I | n*(z.2:ℝ)≤(i:ℝ)+1})
  exact (isClosed_le continuous_const (by fun_prop)).inter
    (isClosed_le (by fun_prop) continuous_const)

lemma strip_cover (n : ℕ) (hn : 0<n) : ⋃ i, strip n i=univ := by
  ext z
  simp only [mem_iUnion,mem_univ,iff_true]
  have ht : 0≤(n:ℝ)*(z.2:ℝ) := mul_nonneg (Nat.cast_nonneg _) z.2.property.1
  let i := min ⌊(n:ℝ)*(z.2:ℝ)⌋₊ (n-1)
  have hi : i<n := (min_le_right ..).trans_lt (by omega)
  refine ⟨⟨i,hi⟩,?_,?_⟩
  · exact (Nat.cast_le.mpr (min_le_left ..)).trans (Nat.floor_le ht)
  · by_cases h : ⌊(n:ℝ)*(z.2:ℝ)⌋₊≤n-1
    · simpa [i,min_eq_left h] using (Nat.lt_floor_add_one ((n:ℝ)*(z.2:ℝ))).le
    · have hin : i=n-1 := min_eq_right (le_of_not_ge h)
      have hn' : ((n-1:ℕ):ℝ)+1=n := by norm_cast; omega
      change (n:ℝ)*(z.2:ℝ)≤(i:ℝ)+1
      rw [hin,hn']
      exact mul_le_of_le_one_right (Nat.cast_nonneg _) z.2.property.2

def coordinate (n : ℕ) (i : Fin n) : C(strip n i,I) :=
  ⟨fun z => ⟨n*(z.val.2:ℝ)-(i:ℝ),by
      have h := z.property
      exact ⟨sub_nonneg.mpr h.1,by linarith [h.2]⟩⟩,by fun_prop⟩

def patch (n : ℕ) (i : Fin n) (F : C(I×I,X)) : C(strip n i,X) :=
  F.comp ⟨fun z => (z.val.1,coordinate n i z),by fun_prop⟩

lemma strip_overlap {n : ℕ} {i j : Fin n} (hij : i<j) {z : I×I}
    (hi : z∈strip n i) (hj : z∈strip n j) :
    (i:ℕ)+1=(j:ℕ) ∧ (n:ℝ)*(z.2:ℝ)=(j:ℝ) := by
  have hij' : (i:ℝ)+1≤(j:ℝ) := by exact_mod_cast hij
  have heq : (i:ℝ)+1=(j:ℝ) := le_antisymm hij' (hj.1.trans hi.2)
  constructor
  · exact_mod_cast heq
  · exact le_antisymm (hi.2.trans heq.le) hj.1

lemma patch_agree (n : ℕ) (F : Fin n → C(I×I,X))
    (hF : ∀ i j : Fin n, (i:ℕ)+1=(j:ℕ) → ∀ s, F i (s,1)=F j (s,0)) :
    ∀ i j z (hi : z∈strip n i) (hj : z∈strip n j),
      patch n i (F i) ⟨z,hi⟩=patch n j (F j) ⟨z,hj⟩ := by
  intro i j z hi hj
  rcases lt_trichotomy i j with hij|rfl|hji
  · obtain ⟨hij',hz⟩ := strip_overlap hij hi hj
    have hci : coordinate n i ⟨z,hi⟩=1 := by
      apply Subtype.ext
      change (n:ℝ)*(z.2:ℝ)-(i:ℝ)=1
      rw [hz]; have hcast : (i:ℝ)+1=(j:ℝ) := by exact_mod_cast hij'
      linarith
    have hcj : coordinate n j ⟨z,hj⟩=0 := by
      apply Subtype.ext; change (n:ℝ)*(z.2:ℝ)-(j:ℝ)=0; rw [hz,sub_self]
    simpa only [patch,ContinuousMap.comp_apply,ContinuousMap.coe_mk,hci,hcj] using hF i j hij' z.1
  · rfl
  · obtain ⟨hji',hz⟩ := strip_overlap hji hj hi
    have hcj : coordinate n j ⟨z,hj⟩=1 := by
      apply Subtype.ext
      change (n:ℝ)*(z.2:ℝ)-(j:ℝ)=1
      rw [hz]; have hcast : (j:ℝ)+1=(i:ℝ) := by exact_mod_cast hji'
      linarith
    have hci : coordinate n i ⟨z,hi⟩=0 := by
      apply Subtype.ext; change (n:ℝ)*(z.2:ℝ)-(i:ℝ)=0; rw [hz,sub_self]
    simpa only [patch,ContinuousMap.comp_apply,ContinuousMap.coe_mk,hci,hcj] using (hF j i hji' z.1).symm

def glue (n : ℕ) (hn : 0<n) (F : Fin n → C(I×I,X))
    (hF : ∀ i j : Fin n, (i:ℕ)+1=(j:ℕ) → ∀ s, F i (s,1)=F j (s,0)) : C(I×I,X) :=
  CannonClosedGluing.glue (strip n) (strip_closed n) (strip_cover n hn)
    (fun i => patch n i (F i)) (patch_agree n F hF)

lemma glue_apply (n : ℕ) (hn : 0<n) (F : Fin n → C(I×I,X))
    (hF : ∀ i j : Fin n, (i:ℕ)+1=(j:ℕ) → ∀ s, F i (s,1)=F j (s,0))
    (i : Fin n) (z : I×I) (hz : z∈strip n i) :
    glue n hn F hF z=F i (z.1,coordinate n i ⟨z,hz⟩) := by
  exact CannonClosedGluing.glue_apply (strip n) (strip_closed n) (strip_cover n hn)
    (fun i => patch n i (F i)) (patch_agree n F hF) i ⟨z,hz⟩

def parameter (n : ℕ) (hn : 0<n) (i : Fin n) : C(I,I) :=
  ⟨fun t => ⟨((i:ℝ)+(t:ℝ))/n,div_nonneg (add_nonneg (Nat.cast_nonneg _) t.property.1) (Nat.cast_nonneg _),
      (div_le_one (by exact_mod_cast hn)).mpr (by
        have hi : (i:ℝ)+1≤n := by exact_mod_cast i.isLt
        linarith [t.property.2])⟩,by fun_prop⟩

lemma parameter_coordinate (n : ℕ) (hn : 0<n) (i : Fin n) (z : strip n i) :
    parameter n hn i (coordinate n i z)=z.val.2 := by
  apply Subtype.ext
  change ((i:ℝ)+((n:ℝ)*(z.val.2:ℝ)-(i:ℝ)))/n=(z.val.2:ℝ)
  field_simp
  ring

@[simp] lemma parameter_zero (n : ℕ) (hn : 0<n) (i : Fin n) :
    parameter n hn i 0=point n hn i.castSucc := by ext; simp [parameter,point]
@[simp] lemma parameter_one (n : ℕ) (hn : 0<n) (i : Fin n) :
    parameter n hn i 1=point n hn i.succ := by ext; simp [parameter,point]

end CannonGrid

namespace CannonGrid
open Set Metric Topology unitInterval

variable {X : Type*} [MetricSpace X]

lemma subdivision_fine (f : C(I,X)) {r : ℝ} (hr : 0<r) :
    ∃ n : ℕ, ∃ hn : 0<n, ∀ (i : Fin n) (t : I),
      dist (f (parameter n hn i t)) (f (point n hn i.castSucc))<r := by
  have hu : UniformContinuous f := CompactSpace.uniformContinuous_of_continuous f.continuous
  obtain ⟨δ,hδ,hclose⟩ := Metric.uniformContinuous_iff.mp hu r hr
  obtain ⟨N,hN⟩ := exists_nat_one_div_lt hδ
  let n := N+1
  have hn : 0<n := Nat.succ_pos N
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  refine ⟨n,hn,fun i t => hclose ?_⟩
  change |((i:ℝ)+(t:ℝ))/n-(i:ℝ)/n|<δ
  rw [← sub_div,add_sub_cancel_left,abs_of_nonneg (div_nonneg t.property.1 hnR.le)]
  exact ((div_le_div_iff_of_pos_right hnR).mpr t.property.2).trans_lt (by simpa [n] using hN)

end CannonGrid

namespace CannonGrid
open Set Metric Topology unitInterval

variable {X : Type*} [TopologicalSpace X]

@[simp] lemma point_zero (n : ℕ) (hn : 0<n) : point n hn 0=0 := by ext; simp [point]
@[simp] lemma point_last (n : ℕ) (hn : 0<n) : point n hn (Fin.last n)=1 := by
  ext; simp [point,ne_of_gt hn]

lemma glue_zero_right (n : ℕ) (hn : 0<n) (F : Fin n → C(I×I,X))
    (hF : ∀ i j : Fin n, (i:ℕ)+1=(j:ℕ) → ∀ s, F i (s,1)=F j (s,0)) (s : I) :
    glue n hn F hF (s,0)=F ⟨0,hn⟩ (s,0) := by
  have hz : (s,0)∈strip n ⟨0,hn⟩ := by simp [strip]
  rw [glue_apply n hn F hF ⟨0,hn⟩ (s,0) hz]
  congr 1
  apply Prod.ext
  · rfl
  apply Subtype.ext
  simp [coordinate]

lemma glue_one_right (n : ℕ) (hn : 0<n) (F : Fin n → C(I×I,X))
    (hF : ∀ i j : Fin n, (i:ℕ)+1=(j:ℕ) → ∀ s, F i (s,1)=F j (s,0)) (s : I) :
    glue n hn F hF (s,1)=F ⟨n-1,by omega⟩ (s,1) := by
  have hn' : ((n-1:ℕ):ℝ)+1=n := by norm_cast; omega
  have hz : (s,1)∈strip n ⟨n-1,by omega⟩ := by
    change ((n-1:ℕ):ℝ)≤n*(1:ℝ) ∧ n*(1:ℝ)≤((n-1:ℕ):ℝ)+1
    constructor <;> linarith
  rw [glue_apply n hn F hF ⟨n-1,by omega⟩ (s,1) hz]
  congr 1
  apply Prod.ext
  · rfl
  apply Subtype.ext
  change (n:ℝ)*1-((n-1:ℕ):ℝ)=1
  linarith

lemma glue_bottom (n : ℕ) (hn : 0<n) (F : Fin n → C(I×I,X))
    (hF : ∀ i j : Fin n, (i:ℕ)+1=(j:ℕ) → ∀ s, F i (s,1)=F j (s,0))
    (f : C(I,X)) (hf : ∀ i t, F i (0,t)=f (parameter n hn i t)) (t : I) :
    glue n hn F hF (0,t)=f t := by
  obtain ⟨i,hi⟩ := mem_iUnion.mp ((strip_cover n hn).symm.subset (mem_univ (0,t)))
  rw [glue_apply n hn F hF i (0,t) hi,hf,parameter_coordinate]

end CannonGrid

namespace CannonLoopApproximation
open Set Metric Topology unitInterval CannonRegularDisk CannonGrid

variable {X : Type*} [MetricSpace X]

theorem loop_approximation {r L C : ℝ} (hr : 0<r) (hL : 1≤L) (_hC : 0<C)
    (T S : Set X)
    (hcover : ∀ x : X, ∃ v∈T, dist x v≤r)
    (hconnect : ∀ x y : X, dist x y≤r →
      ∃ p : Path x y, ∀ t, dist (p t) x≤L*r)
    (hjoin : ∀ x∈T, ∀ y∈T, dist x y<4*r →
      ∃ p : Path x y, range p⊆S ∧ ∀ t, dist (p t) x≤3*L*r)
    (hdisks : ∀ x : X, ∃ U : Set X, IsRegularDisk U ∧
      ball x ((3*L+2)*r)⊆U ∧ U⊆ball x (C*r))
    (f : C(I,X)) (hf : f 0=f 1) :
    ∃ H : C(I×I,X), (∀ t, H (0,t)=f t) ∧
      (∀ t, H (1,t)∈S) ∧ (∀ s, H (s,0)=H (s,1)) ∧
      (∀ s s' t, dist (H (s,t)) (H (s',t))<2*C*r) := by
  classical
  choose v hvT hvd using hcover
  choose c hcd using fun x => hconnect x (v x) (hvd x)
  obtain ⟨n,hn,hnfine⟩ := subdivision_fine f hr
  let p (i : Fin (n+1)) := f (point n hn i)
  have hstep (i : Fin n) : dist (p i.succ) (p i.castSucc)<r := by
    simpa only [parameter_one] using hnfine i 1
  have hvstep (i : Fin n) : dist (v (p i.castSucc)) (v (p i.succ))<4*r := by
    have h := dist_triangle4 (v (p i.castSucc)) (p i.castSucc) (p i.succ) (v (p i.succ))
    have h₀ := hvd (p i.castSucc)
    have h₁ := hvd (p i.succ)
    rw [dist_comm (v (p i.castSucc)) (p i.castSucc),dist_comm (p i.castSucc) (p i.succ)] at h
    linarith [hstep i]
  choose b hbS hbd using fun i : Fin n =>
    hjoin _ (hvT (p i.castSucc)) _ (hvT (p i.succ)) (hvstep i)
  choose U hU hUin hUout using fun i : Fin n => hdisks (p i.castSucc)
  have haU (i : Fin n) : range (f.comp (parameter n hn i))⊆U i := by
    rintro _ ⟨t,rfl⟩
    apply hUin i
    change dist (f (parameter n hn i t)) (p i.castSucc)<(3*L+2)*r
    nlinarith [hnfine i t]
  have hbU (i : Fin n) : range (b i)⊆U i := by
    rintro _ ⟨t,rfl⟩
    apply hUin i
    change dist (b i t) (p i.castSucc)<(3*L+2)*r
    have h := dist_triangle (b i t) (v (p i.castSucc)) (p i.castSucc)
    rw [dist_comm (v (p i.castSucc)) (p i.castSucc)] at h
    nlinarith [hbd i t,hvd (p i.castSucc)]
  have hcU (i : Fin n) : range (c (p i.castSucc))⊆U i := by
    rintro _ ⟨t,rfl⟩
    apply hUin i
    change dist (c (p i.castSucc) t) (p i.castSucc)<(3*L+2)*r
    nlinarith [hcd (p i.castSucc) t]
  have hdU (i : Fin n) : range (c (p i.succ))⊆U i := by
    rintro _ ⟨t,rfl⟩
    apply hUin i
    change dist (c (p i.succ) t) (p i.castSucc)<(3*L+2)*r
    have h := dist_triangle (c (p i.succ) t) (p i.succ) (p i.castSucc)
    nlinarith [hcd (p i.succ) t,hstep i]
  have hfill (i : Fin n) : ∃ F : C(I×I,X), (∀ z, F z∈U i) ∧
      (∀ t, F (0,t)=f (parameter n hn i t)) ∧
      (∀ t, F (1,t)=b i t) ∧
      (∀ s, F (s,0)=c (p i.castSucc) s) ∧ (∀ s, F (s,1)=c (p i.succ) s) := by
    exact (hU i).fill_square (f.comp (parameter n hn i)) (b i).toContinuousMap
      (c (p i.castSucc)).toContinuousMap (c (p i.succ)).toContinuousMap
      (by simp [p]) (by simp [p]) (by simp) (by simp) (haU i) (hbU i) (hcU i) (hdU i)
  choose F hFU hFa hFb hFc hFd using hfill
  have hFF (i j : Fin n) (hij : (i:ℕ)+1=(j:ℕ)) (s : I) : F i (s,1)=F j (s,0) := by
    rw [hFd,hFc]
    have heq : i.succ=j.castSucc := Fin.ext hij
    rw [heq]
  let H := glue n hn F hFF
  refine ⟨H,glue_bottom n hn F hFF f hFa,?_,?_,?_⟩
  · intro t
    obtain ⟨i,hi⟩ := mem_iUnion.mp ((strip_cover n hn).symm.subset (mem_univ (1,t)))
    rw [show H (1,t)=_ from glue_apply n hn F hFF i (1,t) hi,hFb]
    exact hbS i (mem_range_self _)
  · intro s
    rw [show H (s,0)=_ from glue_zero_right n hn F hFF s,
      show H (s,1)=_ from glue_one_right n hn F hFF s,hFc,hFd]
    have hlast : (⟨n-1,by omega⟩ : Fin n).succ=Fin.last n := Fin.ext (by simp; omega)
    have hzero : (⟨0,hn⟩ : Fin n).castSucc=0 := rfl
    have hp : p (⟨0,hn⟩ : Fin n).castSucc=p (⟨n-1,by omega⟩ : Fin n).succ := by
      simp only [hlast,hzero,p,point_zero,point_last,hf]
    exact congrArg (fun x => c x s) hp
  · intro s s' t
    obtain ⟨i,hi⟩ := mem_iUnion.mp ((strip_cover n hn).symm.subset (mem_univ (s,t)))
    have hi' : (s',t)∈strip n i := hi
    rw [show H (s,t)=_ from glue_apply n hn F hFF i (s,t) hi,
      show H (s',t)=_ from glue_apply n hn F hFF i (s',t) hi']
    have h₀ := hUout i (hFU i (s,coordinate n i ⟨(s,t),hi⟩))
    have h₁ := hUout i (hFU i (s',coordinate n i ⟨(s',t),hi'⟩))
    have h := dist_triangle (F i (s,coordinate n i ⟨(s,t),hi⟩)) (p i.castSucc)
      (F i (s',coordinate n i ⟨(s',t),hi'⟩))
    rw [dist_comm (p i.castSucc)] at h
    change dist _ _<C*r at h₀ h₁
    linarith

end CannonLoopApproximation

namespace CannonRelease
open Set Metric Topology unitInterval CannonGraph CannonRegularDisk CannonEmbeddedArc CannonEmbeddedArc.Arc

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

theorem boundary_uniform_loop_graph (φ : Boundary D ≃ₜ SphereTwo) :
    let _ := visualMetricSpace D hδ
    ∃ A B r₀ : ℝ, 1≤A ∧ 0<B ∧ 0<r₀ ∧ ∃ K : ℕ,
      ∀ r : ℝ, 0<r → r≤r₀ → ∀ T : Finset (Boundary D),
      (∀ x∈T, ∀ y∈T, x≠y → r≤dist x y) →
      (∀ x : Boundary D, ∃ y∈T, dist x y≤r) →
      ∃ n : ℕ, ∃ F : Fin n → Arc (Boundary D),
        Pairwise (fun e f => Compatible (F e) (F f)) ∧
        (∀ j, diam (range (F j))≤A*r) ∧
        (∀ x, intersectionCount F (ball x (2*A*r))≤K) ∧
        (∀ (f : C(I,Boundary D)), f 0=f 1 →
          ∃ H : C(I×I,Boundary D), (∀ t, H (0,t)=f t) ∧
            (∀ t, H (1,t)∈(⋃ j, range (F j))∪(T:Set (Boundary D))) ∧
            (∀ s, H (s,0)=H (s,1)) ∧
            (∀ s s' t, dist (H (s,t)) (H (s',t))<B*r)) := by
  let _ := visualMetricSpace D hδ
  dsimp only
  obtain ⟨A,rG,hA,hrG,K,hgraph⟩ := boundary_uniform_embedded_graph D hδ φ
  obtain ⟨L,rA,hL,hrA,harc⟩ := boundary_controlled_embedded_arcs D hδ φ
  obtain ⟨c,hc,_,hdisks⟩ := boundary_controlled_regular_disks D hδ φ
  let M := max A L
  have hM : 1≤M := hA.trans (le_max_left ..)
  have hMp : 0<3*M+2 := by linarith
  let C := (3*M+2)/c
  have hC : 0<C := div_pos hMp hc
  refine ⟨A,2*C,min rG (min rA (c/(3*M+2))),hA,by positivity,
    lt_min hrG (lt_min hrA (div_pos hc hMp)),K,?_⟩
  intro r hr hrs T hsep hcover
  obtain ⟨n,F,hFc,hFj,hFd,hFt⟩ := hgraph r hr (hrs.trans (min_le_left ..)) T hsep
  refine ⟨n,F,hFc,hFd,hFt,?_⟩
  intro f hf
  have hcon (x y : Boundary D) (hd : dist x y≤r) :
      ∃ p : Path x y, ∀ t, dist (p t) x≤M*r := by
    by_cases heq : x=y
    · subst y
      exact ⟨Path.refl x,fun t => by simp; positivity⟩
    · obtain ⟨a,ha₀,ha₁,hs,_⟩ := harc r hr
        (hrs.trans ((min_le_right ..).trans (min_le_left ..))) x y heq (by linarith)
      refine ⟨⟨a.map,ha₀,ha₁⟩,fun t => ?_⟩
      have h := hs (mem_range_self t)
      change dist (a t) x<L*r at h
      exact h.le.trans (mul_le_mul_of_nonneg_right (le_max_right ..) hr.le)
  have hj (x : Boundary D) (hx : x∈(T:Set (Boundary D)))
      (y : Boundary D) (hy : y∈(T:Set (Boundary D))) (hd : dist x y<4*r) :
      ∃ p : Path x y, range p⊆(⋃ j, range (F j))∪(T:Set (Boundary D)) ∧
        ∀ t, dist (p t) x≤3*M*r := by
    by_cases heq : x=y
    · subst y
      refine ⟨Path.refl x,?_,fun t => by simp; positivity⟩
      rintro z ⟨t,rfl⟩
      exact Or.inr hx
    · obtain ⟨_,_,b,hb₀,hb₁,hbs,hbd⟩ := hFj x hx y hy heq hd
      refine ⟨⟨b.map,hb₀,hb₁⟩,hbs.trans subset_union_left,fun t => ?_⟩
      have h := dist_le_diam_of_mem b.compact_range.isBounded (mem_range_self t) (mem_range_self 0)
      rw [hb₀] at h
      exact h.trans (hbd.trans (by nlinarith [le_max_left A L]))
  have hds (x : Boundary D) : ∃ U : Set (Boundary D), IsRegularDisk U ∧
      ball x ((3*M+2)*r)⊆U ∧ U⊆ball x (C*r) := by
    have hs₁ : C*r≤1 := by
      have hh := hrs.trans ((min_le_right ..).trans (min_le_right ..))
      have hh' := (le_div_iff₀ hMp).mp hh
      dsimp only [C]
      rw [div_mul_eq_mul_div]
      apply (div_le_one hc).mpr
      nlinarith [hh']
    obtain ⟨U,hU,hin,hout⟩ := hdisks x (C*r) (mul_pos hC hr) hs₁
    have heq : c*(C*r)=(3*M+2)*r := by dsimp [C]; field_simp
    exact ⟨U,hU,by simpa only [heq] using hin,subset_closure.trans hout⟩
  simpa only [mul_assoc] using CannonLoopApproximation.loop_approximation hr hM hC
    (T:Set (Boundary D)) ((⋃ j, range (F j))∪(T:Set (Boundary D)))
    hcover hcon hj hds f hf

end CannonRelease

end
end
end
end
end
end

end OAI
