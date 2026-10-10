import OAI.Probability.CriticalZ3.Relay

namespace OAI

universe uOmega

open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
namespace Model

def Internal : (m : Model) → Set Vertex → m.Bit → Prop
  | .bond,D,e => e.1 ∈ D ∧ step e.1 e.2 ∈ D
  | .site,D,x => x ∈ D

def UniformOn (m : Model) (p : m.Bit → Set.Icc (0:ℝ) 1)
    (q : Set.Icc (0:ℝ) 1) (D : Set Vertex) : Prop := ∀ e, m.Internal D e → p e = q

theorem box_internal (m : Model) (B : Box) (e : m.Bit) :
    e ∈ B.bits m ↔ m.Internal {x | B.Contains x} e := by
  cases m <;> simp [Box.bits,Internal]

theorem internal_mono (m : Model) {D T : Set Vertex} (h : D ⊆ T) {e : m.Bit}
    (he : m.Internal D e) : m.Internal T e := by
  cases m
  · exact ⟨h he.1,h he.2⟩
  · exact h he

theorem UniformOn.box (m : Model) {p : m.Bit → Set.Icc (0:ℝ) 1} {q : Set.Icc (0:ℝ) 1}
    {D : Set Vertex} (h : m.UniformOn p q D) (B : Box) (hB : ∀ x, B.Contains x → x ∈ D) :
    ∀ e ∈ B.bits m, p e = q := fun e he => h e (m.internal_mono hB ((m.box_internal B e).mp he))

theorem seedReaches_target_mono (m : Model) (c : Vertex) (a b : ℕ) {T U : Set Vertex} (h : T ⊆ U) :
    m.SeedReaches c a b T ⊆ m.SeedReaches c a b U := by
  rintro ω ⟨x,hx,ho,y,hy,hp⟩
  exact ⟨x,hx,ho,y,h hy,hp⟩

theorem seedReaches_image_probability (m : Model) (S : SignedSymmetry) (q : Set.Icc (0:ℝ) 1)
    (c : Vertex) (a b : ℕ) (hab : a ≤ b) (T : Set Vertex) :
    (ProductCylinder.law (fun _ : m.Bit => q)).real
      (m.SeedReaches (S.vertex c) a b (S.vertex '' T)) =
    (ProductCylinder.law (fun _ : m.Bit => q)).real (m.SeedReaches c a b T) := by
  have he : S.vertex ⁻¹' (S.vertex '' T) = T := Set.preimage_image_eq T S.vertex.injective
  cases m
  · simp only [seedReaches_bond,Measure.real_def]
    have hh := ProductCylinder.reindex_probability S.bond q (bondSeedReaches c a b T)
      (measurableSet_bondSeedReaches _ _ _ _)
    rw [←hh]
    congr 2
    ext ω
    simpa only [Set.mem_preimage,he] using (S.bondSeedReaches_map ω c a b (S.vertex '' T)).symm
  · simp only [seedReaches_site,Measure.real_def]
    have hh := ProductCylinder.reindex_probability S.vertex q (siteSeedReaches c a b T)
      (measurableSet_siteSeedReaches _ _ _ hab _)
    rw [←hh]
    congr 2
    ext ω
    simpa only [Set.mem_preimage,he] using (S.siteSeedReaches_map ω c a b (S.vertex '' T)).symm
end Model

namespace LatticeGraph
variable (G : LatticeGraph)
def ContainsSet (D : Set Vertex) : Prop :=
  (∀ x ∈ D, x ∈ G.vertices) ∧ ∀ e : Bond, e.1 ∈ D → step e.1 e.2 ∈ D → e ∈ G.edges

theorem ContainsSet.box {D : Set Vertex} (h : G.ContainsSet D) (B : Box)
    (hB : ∀ x, B.Contains x → x ∈ D) : G.ContainsBox B := by
  constructor
  · intro x hx; exact h.1 x (hB x (Box.mem_vertices B x |>.mp hx))
  · intro e he
    have hh := (Box.mem_bonds B e).mp he
    exact h.2 e (hB _ hh.1) (hB _ hh.2)
end LatticeGraph

namespace Box

def rect (c w : Vertex) (hw : ∀ i, 0 ≤ w i) : Box :=
  ⟨fun i => c i-w i,fun i => c i+w i,fun i => by linarith [hw i]⟩

theorem contains_rect (c w : Vertex) (hw : ∀ i, 0 ≤ w i) (x : Vertex) :
    (rect c w hw).Contains x ↔ x ∈ LatticeRelay.Rect c w := by
  constructor <;> intro h i
  · have hh := h i
    change |x i-c i| ≤ w i
    rw [abs_le]
    dsimp [rect] at hh
    omega
  · have hh := h i
    change |x i-c i| ≤ w i at hh
    rw [abs_le] at hh
    change c i-w i ≤ x i ∧ x i ≤ c i+w i
    omega

def framedRect (S : SignedSymmetry) (c w : Vertex) (hw : ∀ i, 0 ≤ w i) : Box :=
  rect (S.vertex c) (fun i => w (S.perm i)) (fun i => hw (S.perm i))

theorem abs_vertex_sub (S : SignedSymmetry) (x c : Vertex) (i : Fin 3) :
    |S.vertex x i-S.vertex c i| = |x (S.perm i)-c (S.perm i)| := by
  dsimp [SignedSymmetry.vertex]
  cases S.signs i <;> simp only [Bool.false_eq_true,ite_false,ite_true]
  · have he : S.shift i+-x (S.perm i)-(S.shift i+-c (S.perm i)) =
        -(x (S.perm i)-c (S.perm i)) := by ring
    rw [he,abs_neg]
  · congr 1; ring

theorem framedRect_map (S : SignedSymmetry) (c w : Vertex) (hw : ∀ i, 0 ≤ w i) (x : Vertex) :
    (framedRect S c w hw).Contains (S.vertex x) ↔ x ∈ LatticeRelay.Rect c w := by
  rw [framedRect,contains_rect]
  change (∀ i, |S.vertex x i-S.vertex c i| ≤ w (S.perm i)) ↔ _
  simp_rw [abs_vertex_sub]
  constructor
  · intro h i; simpa only [Equiv.apply_symm_apply] using h (S.perm.symm i)
  · intro h i; exact h _

theorem framedRect_expand_map (S : SignedSymmetry) (c w : Vertex) (hw : ∀ i, 0 ≤ w i)
    (R : ℕ) (x : Vertex) :
    ((framedRect S c w hw).expand R).Contains (S.vertex x) ↔ x ∈ LatticeRelay.Expand c w R := by
  have he : (framedRect S c w hw).expand R =
      framedRect S c (fun i => w i+R) (fun i => by have := hw i; positivity) := by
    apply Box.ext <;> funext i <;> dsimp [expand,framedRect,rect] <;> ring
  rw [he,framedRect_map]
  rfl
end Box

namespace ScaleData
variable {model : Model} (s : ScaleData model)

theorem radius_seed {n : ℕ} (hn : n ∈ ({2*s.r,2*s.r+1,10*s.r} : Finset ℕ)) : s.seed ≤ n := by
  have := s.seed_R
  have := s.large_r
  simp only [Finset.mem_insert,Finset.mem_singleton] at hn
  omega

theorem extension_interface (G : LatticeGraph) (p : model.Bit → Set.Icc (0:ℝ) 1)
    (D : Set Vertex) (hG : G.ContainsSet D) (hp : model.UniformOn p s.q D)
    (o : G.Node) (ho : o.1 ∉ D) (B : Box) (T : Set Vertex)
    (hB : ∀ x, (B.expand s.R).Contains x → x ∈ D)
    (hI : ∀ u, (B.expand s.R).Contains u → ∃ n ∈ ({2*s.r,2*s.r+1,10*s.r}:Finset ℕ),
      ∃ S : SignedSymmetry, ∃ c : Vertex, ∃ f : FaceIndex, S.vertex c = u ∧
      (∀ x ∈ cube u n, x ∈ D) ∧ S.vertex '' QuarterFace c n f ⊆ T) :
    (ProductCylinder.law p).real {ω | G.Meets model ω o {x | B.Contains x} ∧
      ¬G.Meets model ω o T} < s.η := by
  refine (G.extension_bound model p s.q s.q_pos s.q_lt.le s.p_lt_one B s.seed s.K s.R
    s.K_pos s.seed_R (hG.box G _ hB) o T (fun h => ho (hB _ h))
    (hp.box model _ hB) s.γ_range.1.le s.τ_range.1 ?_).trans_lt s.extension_budget
  intro u hu
  obtain ⟨n,hn,S,c,f,hc,hcube,hface⟩ := hI u hu
  have hr := s.radius_seed hn
  refine ⟨n,hr,hG.box G _ (fun x hx => hcube x (Box.contains_cube_iff.mp hx)),?_⟩
  have he := ProductCylinder.probability_congr_parameters ((Box.cube u n).bits model)
    p (fun _ => s.q) (hp.box model _ (fun x hx => hcube x (Box.contains_cube_iff.mp hx)))
    (model.SeedReaches u s.seed n T) (model.seedReaches_determined _ _ _ hr _)
  rw [he]
  have hh := s.faces n hn c f
  rw [←model.seedReaches_image_probability S s.q c s.seed n hr (QuarterFace c n f),hc] at hh
  exact hh.le.trans (measureReal_mono (model.seedReaches_target_mono _ _ _ hface))
end ScaleData
end CriticalZ3

namespace MeasureTheory
open scoped _root_.MeasureTheory
open Classical
variable {Ω : Type uOmega} [MeasurableSpace Ω]
theorem finite_relay_bound (μ : _root_.MeasureTheory.Measure Ω) [_root_.MeasureTheory.IsProbabilityMeasure μ] (A : ℕ → Set Ω)
    (η : ℝ) (n : ℕ) (h : ∀ i < n, μ.real (A i \ A (i+1)) ≤ η) :
    μ.real (A 0 \ A n) ≤ n*η := by
  induction n with
  | zero => simp only [Nat.cast_zero,zero_mul,Set.sdiff_self,_root_.MeasureTheory.measureReal_empty,le_refl]
  | succ n ih =>
    have hs : A 0 \ A (n+1) ⊆ (A 0 \ A n) ∪ (A n \ A (n+1)) := by
      intro ω hω
      by_cases hn : ω ∈ A n
      · exact Or.inr ⟨hn,hω.2⟩
      · exact Or.inl ⟨hω.1,hn⟩
    have hh := (_root_.MeasureTheory.measureReal_mono (μ := μ) hs).trans (_root_.MeasureTheory.measureReal_union_le _ _)
    have hi := ih (fun i hi => h i (by omega))
    have hn := h n (by omega)
    rw [Nat.cast_add,Nat.cast_one]
    nlinarith
end MeasureTheory

namespace CriticalZ3
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
namespace ScaleData
variable {model : Model} (s : ScaleData model)

theorem R_pos : 0 < s.R := s.seed_pos.trans s.seed_R

theorem route_width_nonneg (i : ℕ) (j : Fin 3) : 0 ≤ LatticeRelay.routeWidths s.r s.R i j := by
  unfold LatticeRelay.routeWidths
  split_ifs
  · dsimp [LatticeRelay.contractionWidths]
    split_ifs <;> positivity
  · positivity

def routeBox (S : SignedSymmetry) (i : ℕ) : Box :=
  Box.framedRect S (LatticeRelay.routeCenter s.r i) (LatticeRelay.routeWidths s.r s.R i)
    (s.route_width_nonneg i)

theorem routeBox_contains (S : SignedSymmetry) (i : ℕ) (x : Vertex) :
    (s.routeBox S i).Contains x ↔ x ∈ S.vertex '' LatticeRelay.P s.r s.R i := by
  rw [←S.vertex.apply_symm_apply x,routeBox,Box.framedRect_map]
  simp only [Set.mem_image,Equiv.apply_eq_iff_eq,exists_eq_right]
  rfl

theorem relay_in_frame (G : LatticeGraph) (p : model.Bit → Set.Icc (0:ℝ) 1)
    (S : SignedSymmetry) (hG : G.ContainsSet (S.vertex '' LatticeRelay.Prism s.r))
    (hp : model.UniformOn p s.q (S.vertex '' LatticeRelay.Prism s.r))
    (o : G.Node) (ho : o.1 ∉ S.vertex '' LatticeRelay.Prism s.r) :
    (ProductCylinder.law p).real
      {ω | G.Meets model ω o (cube (S.vertex 0) (4*s.r)) ∧
        ¬G.Meets model ω o (cube (S.vertex (LatticeRelay.axisCenter (20*s.r+1))) (4*s.r))}
      ≤ 13*s.η := by
  have hR : (0:ℤ) < s.R := by exact_mod_cast s.R_pos
  have hr : (100:ℤ)*(s.R+1) < s.r := by exact_mod_cast s.large_r
  have hcube (c : Vertex) (n : ℕ) : S.vertex '' LatticeRelay.Cube c n = cube (S.vertex c) n := by
    ext x
    rw [←S.vertex.apply_symm_apply x]
    simp only [Set.mem_image,Equiv.apply_eq_iff_eq,exists_eq_right]
    rw [←S.cube_map]
    rw [mem_cube]
    constructor <;> intro h i
    · have hh := h i
      change |S.vertex.symm x i-c i| ≤ (n:ℤ) at hh
      rw [abs_le] at hh
      change c i-n ≤ S.vertex.symm x i ∧ S.vertex.symm x i ≤ c i+n
      omega
    · have hh := h i
      change c i-n ≤ S.vertex.symm x i ∧ S.vertex.symm x i ≤ c i+n at hh
      change |S.vertex.symm x i-c i| ≤ (n:ℤ)
      rw [abs_le]
      omega
  let A (i : ℕ) : Set model.Config := {ω | G.Meets model ω o {x | (s.routeBox S i).Contains x}}
  have hi (i : ℕ) (hi : i < 13) : (ProductCylinder.law p).real (A i \ A (i+1)) ≤ s.η := by
    apply le_of_lt
    apply s.extension_interface G p (S.vertex '' LatticeRelay.Prism s.r) hG hp o ho
      (s.routeBox S i) {x | (s.routeBox S (i+1)).Contains x}
    · intro x hx
      refine ⟨S.vertex.symm x,?_,S.vertex.apply_symm_apply x⟩
      apply LatticeRelay.expanded_route_subset_prism hR hr hi
      apply (Box.framedRect_expand_map S _ _ (s.route_width_nonneg i) s.R (S.vertex.symm x)).mp
      simpa only [routeBox,Equiv.apply_symm_apply] using hx
    · intro u hu
      have huu : S.vertex.symm u ∈ LatticeRelay.Expand
          (LatticeRelay.routeCenter s.r i) (LatticeRelay.routeWidths s.r s.R i) s.R := by
        apply (Box.framedRect_expand_map S _ _ (s.route_width_nonneg i) s.R (S.vertex.symm u)).mp
        simpa only [routeBox,Equiv.apply_symm_apply] using hu
      obtain ⟨n,hn,hsub,j,signs,hface⟩ := LatticeRelay.thirteen_interfaces hR hr hi _ huu
      have hn' : ∃ l ∈ ({2*s.r,2*s.r+1,10*s.r}:Finset ℕ), (l:ℤ) = n := by
        simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hn
        rcases hn with rfl|rfl|rfl
        · exact ⟨2*s.r,by simp,by push_cast; rfl⟩
        · exact ⟨2*s.r+1,by simp,by push_cast; rfl⟩
        · exact ⟨10*s.r,by simp,by push_cast; rfl⟩
      obtain ⟨l,hl,rfl⟩ := hn'
      refine ⟨l,hl,S,S.vertex.symm u,(j,signs),S.vertex.apply_symm_apply u,?_,?_⟩
      · intro x hx
        have hx' : x ∈ S.vertex '' LatticeRelay.Cube (S.vertex.symm u) l := by
          rw [hcube,S.vertex.apply_symm_apply]
          exact hx
        obtain ⟨y,hy,rfl⟩ := hx'
        exact ⟨y,hsub hy,rfl⟩
      · rintro x ⟨y,hy,rfl⟩
        apply (s.routeBox_contains S (i+1) _).mpr
        exact ⟨y,hface hy,rfl⟩
  have h := finite_relay_bound (ProductCylinder.law p) A s.η 13 hi
  norm_num only [Nat.cast_ofNat] at h
  apply le_trans (measureReal_mono (μ := ProductCylinder.law p) ?_) h
  intro ω hω
  constructor
  · obtain ⟨y,hy,hconn⟩ := hω.1
    refine ⟨y,?_,hconn⟩
    apply (s.routeBox_contains S 0 _).mpr
    rw [LatticeRelay.P_zero,show (4:ℤ)*s.r = (4*s.r:ℕ) by push_cast; rfl,hcube]
    exact hy
  · intro hh
    apply hω.2
    obtain ⟨y,hy,hconn⟩ := hh
    refine ⟨y,?_,hconn⟩
    have hy' := (s.routeBox_contains S 13 _).mp hy
    obtain ⟨z,hz,hzy⟩ := hy'
    rw [←hzy]
    have hz' := LatticeRelay.P_thirteen_subset hR hr hz
    have hm : S.vertex z ∈ S.vertex '' LatticeRelay.Cube (LatticeRelay.axisCenter (20*s.r+1)) (4*s.r:ℕ) :=
      ⟨z,by simpa only [Nat.cast_mul,Nat.cast_ofNat] using hz',rfl⟩
    rwa [hcube] at hm
end ScaleData
end CriticalZ3

end OAI
