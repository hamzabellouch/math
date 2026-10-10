import OAI.AlgebraicTopology.Cubical.Singular
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

namespace OAI

noncomputable section

open Classical Set Topology

namespace EilenbergGanea.PathTransport
open Set CubicalSingular
variable {X : Type*} [TopologicalSpace X] {G : Type*} [Group G]

structure Local (U : Set (Set X)) where
  value : Cube₁ X → G
  constant : ∀ x, value (ContinuousMap.const I x) = 1
  split : ∀ γ ∈ CubicalMesh.small U, value γ = value (cut₁ γ false) * value (cut₁ γ true)
  square : ∀ σ ∈ CubicalMesh.small U,
    value (edge₂ σ 0) * value (edge₁ σ 1) = value (edge₁ σ 0) * value (edge₂ σ 1)

namespace Local
variable {U : Set (Set X)} (l : Local (G:=G) U)

def fold : ℕ → Cube₁ X → G
  | 0, γ => l.value γ
  | n+1, γ => fold n (cut₁ γ false) * fold n (cut₁ γ true)

def Good₁ (n : ℕ) (γ : Cube₁ X) : Prop :=
  CubicalMesh.shrinking (1/2:ℝ) γ n ⊆ CubicalMesh.small U
def Good₂ (n : ℕ) (σ : Cube₂ X) : Prop :=
  CubicalMesh.shrinking (1/2:ℝ) σ n ⊆ CubicalMesh.small U

omit [Group G] in
theorem small_comp {D E : Type*} [MetricSpace D] [MetricSpace E]
    {γ : C(D,X)} (h : γ ∈ CubicalMesh.small U) (f : C(E,D)) :
    γ.comp f ∈ CubicalMesh.small U := by
  obtain ⟨u,hu,hγ⟩ := h
  refine ⟨u,hu,?_⟩
  rintro y ⟨x,hx⟩
  exact hx ▸ hγ ⟨f x,rfl⟩

omit [Group G] in
theorem good₁_zero {γ : Cube₁ X} (h : Good₁ (U:=U) 0 γ) : γ ∈ CubicalMesh.small U := by
  apply h
  exact ⟨ContinuousMap.id I,by simp,rfl⟩
omit [Group G] in
theorem good₂_zero {σ : Cube₂ X} (h : Good₂ (U:=U) 0 σ) : σ ∈ CubicalMesh.small U := by
  apply h
  exact ⟨ContinuousMap.id (I × I),by simp,rfl⟩

omit [Group G] in
theorem good₁_cut {n : ℕ} {γ : Cube₁ X} (h : Good₁ (U:=U) (n+1) γ) (b : Bool) :
    Good₁ (U:=U) n (cut₁ γ b) := by
  rintro τ ⟨f,hf,rfl⟩
  apply h
  refine ⟨(half b).comp f,?_,rfl⟩
  intro x y
  change dist (half b (f x)) (half b (f y)) ≤ _
  rw [half_dist]
  calc
    (1/2:ℝ) * dist (f x) (f y) ≤ (1/2:ℝ) * ((1/2:ℝ)^n * dist x y) :=
      mul_le_mul_of_nonneg_left (hf x y) (by norm_num)
    _ = (1/2:ℝ)^(n+1) * dist x y := by rw [pow_succ]; ring

omit [Group G] in
theorem good₂_cut {n : ℕ} {σ : Cube₂ X} (h : Good₂ (U:=U) (n+1) σ) (b c : Bool) :
    Good₂ (U:=U) n (cut₂ σ b c) := by
  rintro τ ⟨f,hf,rfl⟩
  apply h
  refine ⟨(half₂ (b,c)).comp f,?_,rfl⟩
  intro x y
  change dist (half₂ (b,c) (f x)) (half₂ (b,c) (f y)) ≤ _
  calc
    _ ≤ (1/2:ℝ) * dist (f x) (f y) := half₂_dist _ _ _
    _ ≤ (1/2:ℝ) * ((1/2:ℝ)^n * dist x y) := mul_le_mul_of_nonneg_left (hf x y) (by norm_num)
    _ = (1/2:ℝ)^(n+1) * dist x y := by rw [pow_succ]; ring

theorem fold_small {γ : Cube₁ X} (h : γ ∈ CubicalMesh.small U) (n : ℕ) :
    l.fold n γ = l.value γ := by
  induction n generalizing γ with
  | zero => rfl
  | succ n ih =>
    change l.fold n (cut₁ γ false) * l.fold n (cut₁ γ true) = _
    rw [ih (γ:=cut₁ γ false) (small_comp h _),ih (γ:=cut₁ γ true) (small_comp h _),← l.split γ h]

theorem fold_stable {n : ℕ} {γ : Cube₁ X} (h : Good₁ (U:=U) n γ) (m : ℕ) (hm : n ≤ m) :
    l.fold m γ = l.fold n γ := by
  induction n generalizing m γ with
  | zero => exact l.fold_small (good₁_zero h) m
  | succ n ih =>
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
    change l.fold k (cut₁ γ false) * l.fold k (cut₁ γ true) = _
    rw [ih (good₁_cut h false) k (by omega),ih (good₁_cut h true) k (by omega)]
    rfl

variable (hU : ∀ u ∈ U, IsOpen u) (hcover : ⋃₀ U = univ)
include hU hcover

omit [Group G] in
theorem good₁_eventually (γ : Cube₁ X) : ∀ᶠ n in Filter.atTop, Good₁ (U:=U) n γ := by
  obtain ⟨N,hN⟩ := CubicalMesh.shrinking_small interval_diameter (by norm_num : (1/2:ℝ) < 1) U hU hcover γ
  exact Filter.eventually_atTop.mpr ⟨N,fun n hn => hN n hn (by norm_num)⟩

omit [Group G] in
theorem good₂_eventually (σ : Cube₂ X) : ∀ᶠ n in Filter.atTop, Good₂ (U:=U) n σ := by
  obtain ⟨N,hN⟩ := CubicalMesh.shrinking_small
    (fun x y : I × I => by rw [Prod.dist_eq,max_le_iff]; exact ⟨interval_diameter _ _,interval_diameter _ _⟩)
    (by norm_num : (1/2:ℝ) < 1) U hU hcover σ
  exact Filter.eventually_atTop.mpr ⟨N,fun n hn => hN n hn (by norm_num)⟩

def depth (γ : Cube₁ X) : ℕ := ((good₁_eventually hU hcover γ).exists).choose

theorem depth_good (γ : Cube₁ X) : Good₁ (U:=U) (depth hU hcover γ) γ :=
  ((good₁_eventually hU hcover γ).exists).choose_spec

def transport (γ : Cube₁ X) : G := l.fold (depth hU hcover γ) γ

theorem transport_eq_fold {n : ℕ} {γ : Cube₁ X} (h : Good₁ (U:=U) n γ) :
    l.transport hU hcover γ = l.fold n γ := by
  let m := max n (depth hU hcover γ)
  exact (l.fold_stable (depth_good hU hcover γ) m (le_max_right _ _)).symm.trans
    (l.fold_stable h m (le_max_left _ _))

theorem transport_small {γ : Cube₁ X} (h : γ ∈ CubicalMesh.small U) :
    l.transport hU hcover γ = l.value γ := l.fold_small h _

theorem transport_const (x : X) : l.transport hU hcover (ContinuousMap.const I x) = 1 := by
  rw [l.transport_small hU hcover,l.constant]
  have hx : x ∈ ⋃₀ U := hcover ▸ mem_univ x
  obtain ⟨u,hu,hx⟩ := hx
  refine ⟨u,hu,?_⟩
  rintro y ⟨t,rfl⟩
  exact hx

omit hU hcover in
theorem four_squares (A B C D E F H K M₀ M₁ N₀ N₁ : G)
    (h₀ : A*M₀ = C*N₀) (h₁ : B*D = M₀*N₁)
    (h₂ : N₀*M₁ = E*F) (h₃ : N₁*H = M₁*K) :
    (A*B)*(D*H) = (C*E)*(F*K) := by
  calc
    _ = A*((B*D)*H) := by simp only [mul_assoc]
    _ = A*((M₀*N₁)*H) := by rw [h₁]
    _ = (A*M₀)*(N₁*H) := by simp only [mul_assoc]
    _ = (C*N₀)*(M₁*K) := by rw [h₀,h₃]
    _ = C*((N₀*M₁)*K) := by simp only [mul_assoc]
    _ = C*((E*F)*K) := by rw [h₂]
    _ = (C*E)*(F*K) := by simp only [mul_assoc]

omit hU hcover in
theorem fold_square {n : ℕ} {σ : Cube₂ X} (h : Good₂ (U:=U) n σ) :
    l.fold n (edge₂ σ 0) * l.fold n (edge₁ σ 1) =
      l.fold n (edge₁ σ 0) * l.fold n (edge₂ σ 1) := by
  induction n generalizing σ with
  | zero => exact l.square σ (good₂_zero h)
  | succ n ih =>
    have h₀ := ih (good₂_cut h false false)
    have h₁ := ih (good₂_cut h true false)
    have h₂ := ih (good₂_cut h false true)
    have h₃ := ih (good₂_cut h true true)
    simp only [edge₁_cut₂,edge₂_cut₂,half_false_zero,half_true_one,half_mid] at h₀ h₁ h₂ h₃
    exact four_squares _ _ _ _ _ _ _ _ _ _ _ _ h₀ h₁ h₂ h₃

theorem transport_square (σ : Cube₂ X) :
    l.transport hU hcover (edge₂ σ 0) * l.transport hU hcover (edge₁ σ 1) =
      l.transport hU hcover (edge₁ σ 0) * l.transport hU hcover (edge₂ σ 1) := by
  have hh := (good₂_eventually hU hcover σ).and
    ((good₁_eventually hU hcover (edge₂ σ 0)).and
    ((good₁_eventually hU hcover (edge₁ σ 1)).and
    ((good₁_eventually hU hcover (edge₁ σ 0)).and
      (good₁_eventually hU hcover (edge₂ σ 1)))))
  obtain ⟨n,hσ,h₀,h₁,h₂,h₃⟩ := hh.exists
  rw [l.transport_eq_fold hU hcover h₀,l.transport_eq_fold hU hcover h₁,
    l.transport_eq_fold hU hcover h₂,l.transport_eq_fold hU hcover h₃]
  exact l.fold_square hσ

end Local
end EilenbergGanea.PathTransport

namespace EilenbergGanea.PathTransport.Local
open Set CubicalSingular
variable {X : Type*} [TopologicalSpace X] {G : Type*} [Group G]
variable {U : Set (Set X)} (l : Local (G:=G) U)
variable (hU : ∀ u ∈ U, IsOpen u) (hcover : ⋃₀ U = univ)

omit [Group G] in
theorem good₁_mono {n m : ℕ} (hnm : n ≤ m) {γ : Cube₁ X} (h : Good₁ (U:=U) n γ) :
    Good₁ (U:=U) m γ := by
  rintro τ ⟨f,hf,rfl⟩
  apply h
  refine ⟨f,?_,rfl⟩
  intro x y
  exact (hf x y).trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_of_le_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) ≤ 1) hnm) dist_nonneg)

theorem transport_split (γ : Cube₁ X) :
    l.transport hU hcover γ = l.transport hU hcover (cut₁ γ false) * l.transport hU hcover (cut₁ γ true) := by
  let n := max (depth hU hcover γ) (max (depth hU hcover (cut₁ γ false)) (depth hU hcover (cut₁ γ true)))
  have hγ : Good₁ (U:=U) (n+1) γ := good₁_mono ((le_max_left _ _).trans (Nat.le_succ n)) (depth_good hU hcover γ)
  have h₀ : Good₁ (U:=U) n (cut₁ γ false) := good₁_mono ((le_max_left _ _).trans (le_max_right _ _)) (depth_good hU hcover _)
  have h₁ : Good₁ (U:=U) n (cut₁ γ true) := good₁_mono ((le_max_right _ _).trans (le_max_right _ _)) (depth_good hU hcover _)
  rw [l.transport_eq_fold hU hcover hγ,l.transport_eq_fold hU hcover h₀,l.transport_eq_fold hU hcover h₁]
  rfl

omit [Group G] in
theorem cut_trans_left {x y z : X} (p : Path x y) (q : Path y z) :
    cut₁ (p.trans q).toContinuousMap false = p.toContinuousMap := by
  apply ContinuousMap.ext
  intro t
  change (p.trans q) (half false t) = p t
  rw [← Path.extend_extends' (p.trans q),Path.extend_trans_of_le_half]
  · have h : 2 * (half false t : ℝ) = (t:ℝ) := by simp [half]; ring
    rw [h,Path.extend_extends']
  · change (t:ℝ)/2 ≤ 1/2
    linarith [t.property.2]

omit [Group G] in
theorem cut_trans_right {x y z : X} (p : Path x y) (q : Path y z) :
    cut₁ (p.trans q).toContinuousMap true = q.toContinuousMap := by
  apply ContinuousMap.ext
  intro t
  change (p.trans q) (half true t) = q t
  rw [← Path.extend_extends' (p.trans q),Path.extend_trans_of_half_le]
  · have h : 2 * (half true t : ℝ) - 1 = (t:ℝ) := by simp [half]; ring
    rw [h,Path.extend_extends']
  · change 1/2 ≤ (1+(t:ℝ))/2
    linarith [t.property.1]

theorem transport_trans {x y z : X} (p : Path x y) (q : Path y z) :
    l.transport hU hcover (p.trans q).toContinuousMap =
      l.transport hU hcover p.toContinuousMap * l.transport hU hcover q.toContinuousMap := by
  rw [l.transport_split,cut_trans_left,cut_trans_right]

theorem transport_homotopy {x y : X} {p q : Path x y} (H : p.Homotopy q) :
    l.transport hU hcover p.toContinuousMap = l.transport hU hcover q.toContinuousMap := by
  have h := l.transport_square hU hcover H.toHomotopy.toContinuousMap
  have e₀ : edge₁ H.toHomotopy.toContinuousMap 0 = p.toContinuousMap := by ext t; simp [edge₁]
  have e₁ : edge₁ H.toHomotopy.toContinuousMap 1 = q.toContinuousMap := by ext t; simp [edge₁]
  have c₀ : edge₂ H.toHomotopy.toContinuousMap 0 = ContinuousMap.const I x := by ext t; simp [edge₂]
  have c₁ : edge₂ H.toHomotopy.toContinuousMap 1 = ContinuousMap.const I y := by ext t; simp [edge₂]
  rw [e₀,e₁,c₀,c₁,l.transport_const,l.transport_const,one_mul,mul_one] at h
  exact h.symm

def quotientTransport {x y : X} : Path.Homotopic.Quotient x y → G :=
  Quotient.lift (fun p => l.transport hU hcover p.toContinuousMap)
    (fun _ _ ⟨H⟩ => l.transport_homotopy hU hcover H)

@[simp] theorem quotientTransport_mk {x y : X} (p : Path x y) :
    l.quotientTransport hU hcover (⟦p⟧ : Path.Homotopic.Quotient x y) =
      l.transport hU hcover p.toContinuousMap := rfl

@[simp] theorem quotientTransport_refl (x : X) :
    l.quotientTransport hU hcover (Path.Homotopic.Quotient.refl x) = 1 := l.transport_const hU hcover x

@[simp] theorem quotientTransport_trans {x y z : X}
    (p : Path.Homotopic.Quotient x y) (q : Path.Homotopic.Quotient y z) :
    l.quotientTransport hU hcover (p.trans q) =
      l.quotientTransport hU hcover p * l.quotientTransport hU hcover q := by
  induction p using Quotient.inductionOn
  induction q using Quotient.inductionOn
  exact l.transport_trans hU hcover _ _

/-- Traversal-order labels are a homomorphism to the opposite, because Mathlib's
fundamental group multiplication is categorical (right path first). -/
def fundamentalHom (x : X) : FundamentalGroup X x →* Gᵐᵒᵖ where
  toFun q := MulOpposite.op (l.quotientTransport hU hcover q)
  map_one' := congrArg MulOpposite.op (l.quotientTransport_refl hU hcover x)
  map_mul' p q := by
    rw [FundamentalGroup.mul_def,l.quotientTransport_trans,MulOpposite.op_mul]

/-- Any multiplicative global path label is completely determined on a sufficiently
small open-cover mesh. This is the uniqueness half of low-dimensional descent. -/
theorem transport_unique (v : Cube₁ X → G)
    (hsplit : ∀ γ, v γ = v (cut₁ γ false) * v (cut₁ γ true))
    (hsmall : ∀ γ ∈ CubicalMesh.small U, v γ = l.value γ) (γ : Cube₁ X) :
    v γ = l.transport hU hcover γ := by
  suffices hh : ∀ n γ, Good₁ (U:=U) n γ → v γ = l.fold n γ by
    exact hh _ γ (depth_good hU hcover γ)
  intro n
  induction n with
  | zero => intro γ h; exact hsmall γ (good₁_zero h)
  | succ n ih =>
    intro γ h
    rw [hsplit γ,ih _ (good₁_cut h false),ih _ (good₁_cut h true)]
    rfl

end EilenbergGanea.PathTransport.Local

namespace EilenbergGanea.PathTransport
open CubicalSingular
variable {X : Type*} [TopologicalSpace X]
local instance : ContractibleSpace I := (convex_Icc (0:ℝ) 1).contractibleSpace ⟨0,by norm_num⟩

abbrev PQ (x y : X) := Path.Homotopic.Quotient x y

def cubePath (γ : Cube₁ X) : Path (γ 0) (γ 1) := ⟨γ,rfl,rfl⟩
abbrev asClass {x y : X} (p : Path x y) : PQ x y := Path.Homotopic.Quotient.mk p

def based {r : X} (q : ∀ x, Path r x) {x y : X} (p : PQ x y) : (FundamentalGroup X r)ᵐᵒᵖ :=
  MulOpposite.op (((asClass (q x)).trans p).trans (asClass (q y)).symm)

theorem based_trans {r x y z : X} (q : ∀ x, Path r x) (p : PQ x y) (s : PQ y z) :
    based q (p.trans s) = based q p * based q s := by
  apply MulOpposite.unop_injective
  change ((asClass (q x)).trans (p.trans s)).trans _ =
    (((asClass (q x)).trans p).trans (asClass (q y)).symm).trans
      (((asClass (q y)).trans s).trans (asClass (q z)).symm)
  simp only [Path.Homotopic.Quotient.trans_assoc]
  rw [← Path.Homotopic.Quotient.trans_assoc (asClass (q y)).symm (asClass (q y)),
    Path.Homotopic.Quotient.symm_trans,Path.Homotopic.Quotient.refl_trans]

@[simp] theorem based_refl {r : X} (q : ∀ x, Path r x) (x : X) :
    based q (Path.Homotopic.Quotient.refl x) = 1 := by
  apply MulOpposite.unop_injective
  change ((asClass (q x)).trans (Path.Homotopic.Quotient.refl x)).trans (asClass (q x)).symm = _
  simp only [Path.Homotopic.Quotient.trans_refl,Path.Homotopic.Quotient.trans_symm]
  rfl

def basedPath {r : X} (q : ∀ x, Path r x) {x y : X} (p : Path x y) : (FundamentalGroup X r)ᵐᵒᵖ :=
  based q (asClass p)

theorem basedPath_congr {r x y x' y' : X} (q : ∀ x, Path r x) (p : Path x y) (p' : Path x' y')
    (h : ∀ t, p t = p' t) : basedPath q p = basedPath q p' := by
  have hx : x = x' := by simpa using h 0
  have hy : y = y' := by simpa using h 1
  subst x'; subst y'
  have hp : p = p' := Path.ext (funext h)
  rw [hp]

theorem basedPath_homotopic {r x y : X} (q : ∀ x, Path r x) {p p' : Path x y}
    (h : Path.Homotopic p p') : basedPath q p = basedPath q p' :=
  congrArg (based q) (Quotient.sound h)

@[simp] theorem basedPath_trans {r x y z : X} (q : ∀ x, Path r x) (p : Path x y) (s : Path y z) :
    basedPath q (p.trans s) = basedPath q p * basedPath q s := by
  exact (congrArg (based q) (Path.Homotopic.Quotient.mk_trans p s)).trans (based_trans q _ _)
@[simp] theorem basedPath_refl {r : X} (q : ∀ x, Path r x) (x : X) : basedPath q (Path.refl x) = 1 := based_refl q x

def holonomy {r : X} (q : ∀ x, Path r x) (γ : Cube₁ X) : (FundamentalGroup X r)ᵐᵒᵖ :=
  basedPath q (cubePath γ)

@[simp] theorem holonomy_path {r x y : X} (q : ∀ x, Path r x) (p : Path x y) :
    holonomy q p.toContinuousMap = basedPath q p := basedPath_congr q _ _ (fun _ => rfl)
@[simp] theorem holonomy_const {r : X} (q : ∀ x, Path r x) (x : X) :
    holonomy q (ContinuousMap.const I x) = 1 := basedPath_refl q x

def halfPath₀ : Path (0 : I) (half true 0) := ⟨half false,half_false_zero,half_mid⟩
def halfPath₁ : Path (half true 0) (1 : I) := ⟨half true,rfl,half_true_one⟩

theorem holonomy_split {r : X} (q : ∀ x, Path r x) (γ : Cube₁ X) :
    holonomy q γ = holonomy q (cut₁ γ false) * holonomy q (cut₁ γ true) := by
  have hp := (SimplyConnectedSpace.paths_homotopic Path.id (halfPath₀.trans halfPath₁)).map γ
  have h := basedPath_homotopic q hp
  rw [Path.map_trans,basedPath_trans] at h
  calc
    holonomy q γ = basedPath q (Path.id.map γ.continuous) := basedPath_congr q _ _ (fun _ => rfl)
    _ = basedPath q (halfPath₀.map γ.continuous) * basedPath q (halfPath₁.map γ.continuous) := h
    _ = _ := congrArg₂ (· * ·)
      (basedPath_congr q (halfPath₀.map γ.continuous) (cubePath (cut₁ γ false)) (fun _ => rfl))
      (basedPath_congr q (halfPath₁.map γ.continuous) (cubePath (cut₁ γ true)) (fun _ => rfl))

def bottom : Path ((0:I),(0:I)) (1,0) := Path.id.prod (Path.refl 0)
def rightSide : Path ((1:I),(0:I)) (1,1) := (Path.refl 1).prod Path.id
def leftSide : Path ((0:I),(0:I)) (0,1) := (Path.refl 0).prod Path.id
def topSide : Path ((0:I),(1:I)) (1,1) := Path.id.prod (Path.refl 1)

theorem square_paths (σ : Cube₂ X) :
    Path.Homotopic ((bottom.map σ.continuous).trans (rightSide.map σ.continuous))
      ((leftSide.map σ.continuous).trans (topSide.map σ.continuous)) := by
  have h := (SimplyConnectedSpace.paths_homotopic (bottom.trans rightSide) (leftSide.trans topSide)).map σ
  simpa only [Path.map_trans] using h

theorem holonomy_square {r : X} (q : ∀ x, Path r x) (σ : Cube₂ X) :
    holonomy q (edge₂ σ 0) * holonomy q (edge₁ σ 1) =
      holonomy q (edge₁ σ 0) * holonomy q (edge₂ σ 1) := by
  have h := basedPath_homotopic q (square_paths σ)
  rw [basedPath_trans,basedPath_trans] at h
  have h₀ := basedPath_congr q (bottom.map σ.continuous) (cubePath (edge₂ σ 0)) (fun _ => rfl)
  have h₁ := basedPath_congr q (rightSide.map σ.continuous) (cubePath (edge₁ σ 1)) (fun _ => rfl)
  have h₂ := basedPath_congr q (leftSide.map σ.continuous) (cubePath (edge₁ σ 0)) (fun _ => rfl)
  have h₃ := basedPath_congr q (topSide.map σ.continuous) (cubePath (edge₂ σ 1)) (fun _ => rfl)
  exact (congrArg₂ (· * ·) h₀ h₁).symm.trans (h.trans (congrArg₂ (· * ·) h₂ h₃))

/-- Actual based-loop holonomy is flat; this is derived from square homotopy in
I², rather than supplied as a geometric assumption. -/
def holonomyLocal {r : X} (q : ∀ x, Path r x) (U : Set (Set X)) :
    Local (G:=(FundamentalGroup X r)ᵐᵒᵖ) U where
  value := holonomy q
  constant := holonomy_const q
  split := fun γ _ => holonomy_split q γ
  square := fun σ _ => holonomy_square q σ

end EilenbergGanea.PathTransport

namespace EilenbergGanea.CubicalSingular
variable {X : Type*} [TopologicalSpace X]

/-- Low-dimensional Mayer–Vietoris injectivity, derived by subdivision. -/
theorem mayerVietoris_injective [ContractibleSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = univ)
    {z : N₁ X} (hz : z ∈ L₁ (U ∩ V))
    {a b : N₂ X} (ha : a ∈ L₂ U) (hb : b ∈ L₂ V) (hda : d₂ a = z) (hdb : d₂ b = z) :
    ∃ c ∈ L₂ (U ∩ V), d₂ c = z := by
  have hcycle : d₂ (a-b) = 0 := by rw [map_sub,hda,hdb,sub_self]
  obtain ⟨w,hw⟩ := exact₂_of_contractible (a-b) hcycle
  obtain ⟨n,hn⟩ := S₃_eventually_small U V hU hV hUV w
  obtain ⟨u,hu,v,hv,huv⟩ := Submodule.mem_sup.mp (hn n le_rfl)
  have he : d₃ u + d₃ v = (SN₂^[n]) a - (SN₂^[n]) b := by
    rw [← map_add,huv,d₃_S₃_iter,hw,← Module.End.pow_apply]
    simpa only [Module.End.pow_apply] using (SN₂ ^ n).map_sub a b
  let c : N₂ X := (SN₂^[n]) a - d₃ u
  have hcU : c ∈ L₂ U := Submodule.sub_mem _ (SN₂_iter_support U ha n) (d₃_support U hu)
  have hc_eq : c = (SN₂^[n]) b + d₃ v := by
    apply sub_eq_iff_eq_add.mpr
    calc
      (SN₂^[n]) a = ((SN₂^[n]) a - (SN₂^[n]) b) + (SN₂^[n]) b := (sub_add_cancel _ _).symm
      _ = (d₃ u + d₃ v) + (SN₂^[n]) b := by rw [he]
      _ = ((SN₂^[n]) b + d₃ v) + d₃ u := by abel
  have hcV : c ∈ L₂ V := by
    rw [hc_eq]
    exact Submodule.add_mem _ (SN₂_iter_support V hb n) (d₃_support V hv)
  have hdc : d₂ c = (SN₁^[n]) z := by
    change d₂ ((SN₂^[n]) a - d₃ u) = _
    rw [map_sub,d₂_SN₂_iter,hda,d₂_d₃,sub_zero]
  refine ⟨c - K₁ n z,?_,?_⟩
  · exact Submodule.sub_mem _ (by rw [L₂_inter]; exact ⟨hcU,hcV⟩) (K₁_support _ hz n)
  · rw [map_sub,hdc,K₁_boundary]
    abel

/-- The other half of the same exact sequence, with literal supported chains. -/
theorem mayerVietoris_surjective [ContractibleSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = univ)
    {z : N₁ X} (hzU : z ∈ L₁ U) (hz : d₁ z = 0) :
    ∃ t ∈ L₁ (U ∩ V), d₁ t = 0 ∧
      (∃ b ∈ L₂ U, d₂ b = t-z) ∧ (∃ b ∈ L₂ V, d₂ b = t) := by
  obtain ⟨a,ha⟩ := exact₁_of_contractible z hz
  obtain ⟨n,hn⟩ := SN₂_eventually_small U V hU hV hUV a
  obtain ⟨u,hu,v,hv,huv⟩ := Submodule.mem_sup.mp (hn n le_rfl)
  have he : d₂ u + d₂ v = (SN₁^[n]) z := by rw [← map_add,huv,d₂_SN₂_iter,ha]
  have ht_eq : d₂ v = (SN₁^[n]) z - d₂ u := by
    apply eq_sub_iff_add_eq.mpr
    rw [add_comm,he]
  refine ⟨d₂ v,?_,d₁_d₂ v,?_,⟨v,hv,rfl⟩⟩
  · rw [L₁_inter]
    refine ⟨?_,d₂_support V hv⟩
    rw [ht_eq]
    exact Submodule.sub_mem _ (SN₁_iter_support U hzU n) (d₂_support U hu)
  · refine ⟨K₁ n z-u,Submodule.sub_mem _ (K₁_support U hzU n) hu,?_⟩
    rw [map_sub,K₁_boundary,ht_eq]
    abel

/-- Cycles and boundaries are actual submodules of normalized singular chains. -/
def cyclesOn (U : Set X) : Submodule ℤ (N₁ X) := L₁ U ⊓ LinearMap.ker d₁
def boundsOn (U : Set X) : Submodule ℤ (N₁ X) := (L₂ U).map d₂

theorem boundsOn_le_cyclesOn (U : Set X) : boundsOn U ≤ cyclesOn U := by
  rintro _ ⟨b,hb,rfl⟩
  exact ⟨d₂_support U hb,d₁_d₂ b⟩

def boundaries (U : Set X) : Submodule ℤ (cyclesOn U) := (boundsOn U).comap (cyclesOn U).subtype
abbrev Homology₁ (U : Set X) := cyclesOn U ⧸ boundaries U

def cycleInclusion {U V : Set X} (h : U ⊆ V) : cyclesOn U →ₗ[ℤ] cyclesOn V :=
  Submodule.inclusion (inf_le_inf_right _ (L₁_mono h))

theorem cycleInclusion_bounds {U V : Set X} (h : U ⊆ V) :
    boundaries U ≤ (boundaries V).comap (cycleInclusion h) := by
  rintro z ⟨b,hb,he⟩
  exact ⟨b,L₂_mono h hb,he⟩

def homologyInclusion {U V : Set X} (h : U ⊆ V) : Homology₁ U →ₗ[ℤ] Homology₁ V :=
  (boundaries U).mapQ (boundaries V) (cycleInclusion h) (cycleInclusion_bounds h)

theorem homologyInclusion_injective [ContractibleSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = univ)
    (hVex : ∀ z : N₁ X, z ∈ L₁ V → d₁ z = 0 → ∃ b ∈ L₂ V, d₂ b = z) :
    Function.Injective (homologyInclusion (Set.inter_subset_left : U ∩ V ⊆ U)) := by
  apply LinearMap.ker_eq_bot.mp
  refine le_antisymm ?_ bot_le
  intro z hz
  obtain ⟨z,rfl⟩ := (boundaries (U ∩ V)).mkQ_surjective z
  change (boundaries U).mkQ (cycleInclusion Set.inter_subset_left z) = 0 at hz
  have hzm := (Submodule.Quotient.mk_eq_zero (boundaries U)).mp hz
  obtain ⟨a,ha,hda⟩ := hzm
  obtain ⟨b,hb,hdb⟩ := hVex z.val (L₁_mono Set.inter_subset_right z.property.1) z.property.2
  obtain ⟨c,hc,hdc⟩ := mayerVietoris_injective U V hU hV hUV z.property.1 ha hb hda hdb
  change (boundaries (U ∩ V)).mkQ z = 0
  exact (Submodule.Quotient.mk_eq_zero (boundaries (U ∩ V))).mpr ⟨c,hc,hdc⟩

theorem homologyInclusion_surjective [ContractibleSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = univ) :
    Function.Surjective (homologyInclusion (Set.inter_subset_left : U ∩ V ⊆ U)) := by
  intro z
  obtain ⟨z,rfl⟩ := (boundaries U).mkQ_surjective z
  obtain ⟨t,ht,htz,⟨b,hb,hdb⟩,_⟩ := mayerVietoris_surjective U V hU hV hUV z.property.1 z.property.2
  let t' : cyclesOn (U ∩ V) := ⟨t,ht,htz⟩
  refine ⟨(boundaries (U ∩ V)).mkQ t',?_⟩
  change (boundaries U).mkQ (cycleInclusion Set.inter_subset_left t') = (boundaries U).mkQ z
  rw [← sub_eq_zero,← map_sub]
  exact (Submodule.Quotient.mk_eq_zero (boundaries U)).mpr ⟨b,hb,hdb⟩

/-- No cellular theorem is assumed: this is the comparison for actual open sets
in an actually contractible space, proved by finite singular subdivision. -/
def mayerVietoris_equiv [ContractibleSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = univ)
    (hVex : ∀ z : N₁ X, z ∈ L₁ V → d₁ z = 0 → ∃ b ∈ L₂ V, d₂ b = z) :
    Homology₁ (U ∩ V) ≃ₗ[ℤ] Homology₁ U :=
  LinearEquiv.ofBijective (homologyInclusion Set.inter_subset_left)
    ⟨homologyInclusion_injective U V hU hV hUV hVex,homologyInclusion_surjective U V hU hV hUV⟩

end EilenbergGanea.CubicalSingular

namespace EilenbergGanea.CubicalSingular
open Set
variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

theorem pushN₁_mapsTo (f : C(X,Y)) {U : Set X} {V : Set Y} (hf : MapsTo f U V) :
    L₁ U ≤ (L₁ V).comap (pushN₁ f) := by
  rw [L₁_span]
  apply Submodule.span_le.mpr
  rintro _ ⟨σ,hσ,rfl⟩
  change pushN₁ f (gen₁ σ) ∈ L₁ V
  simp only [gen₁,pushN₁_mk,push₁_single]
  change gen₁ (f.comp σ) ∈ L₁ V
  exact gen₁_mem (by rintro _ ⟨t,rfl⟩; exact hf (hσ ⟨t,rfl⟩))

theorem pushN₂_mapsTo (f : C(X,Y)) {U : Set X} {V : Set Y} (hf : MapsTo f U V) :
    L₂ U ≤ (L₂ V).comap (pushN₂ f) := by
  rw [L₂_span]
  apply Submodule.span_le.mpr
  rintro _ ⟨σ,hσ,rfl⟩
  change pushN₂ f (gen₂ σ) ∈ L₂ V
  simp only [gen₂,pushN₂_mk,push₂_single]
  change gen₂ (f.comp σ) ∈ L₂ V
  exact gen₂_mem (by rintro _ ⟨t,rfl⟩; exact hf (hσ ⟨t,rfl⟩))

@[simp] theorem L₁_univ : L₁ (univ : Set X) = ⊤ := by
  rw [L₁,raw₁,cubeSet_univ,Finsupp.supported_univ,Submodule.map_top]
  exact LinearMap.range_eq_top.mpr (D₁ X).mkQ_surjective
@[simp] theorem L₂_univ : L₂ (univ : Set X) = ⊤ := by
  rw [L₂,raw₂,cubeSet_univ,Finsupp.supported_univ,Submodule.map_top]
  exact LinearMap.range_eq_top.mpr (D₂ X).mkQ_surjective

def cycleMap (f : C(X,Y)) {U : Set X} {V : Set Y} (hf : MapsTo f U V) :
    cyclesOn U →ₗ[ℤ] cyclesOn V :=
  (pushN₁ f).restrict (fun z hz => ⟨pushN₁_mapsTo f hf hz.1,by
    change d₁ (pushN₁ f z) = 0
    rw [d₁_push,hz.2,map_zero]⟩)

theorem cycleMap_bounds (f : C(X,Y)) {U : Set X} {V : Set Y} (hf : MapsTo f U V) :
    boundaries U ≤ (boundaries V).comap (cycleMap f hf) := by
  rintro z ⟨b,hb,he⟩
  refine ⟨pushN₂ f b,pushN₂_mapsTo f hf hb,?_⟩
  exact (d₂_push f b).trans (congrArg (pushN₁ f) he)

def homologyMap (f : C(X,Y)) {U : Set X} {V : Set Y} (hf : MapsTo f U V) :
    Homology₁ U →ₗ[ℤ] Homology₁ V :=
  (boundaries U).mapQ (boundaries V) (cycleMap f hf) (cycleMap_bounds f hf)

@[simp] theorem homologyMap_mk (f : C(X,Y)) {U : Set X} {V : Set Y} (hf : MapsTo f U V)
    (z : cyclesOn U) : homologyMap f hf ((boundaries U).mkQ z) =
      (boundaries V).mkQ (cycleMap f hf z) := rfl

def normalizedPrism {f g : C(X,Y)} (H : f.Homotopy g) : N₁ X →ₗ[ℤ] N₂ Y :=
  (D₁ X).liftQ ((D₂ Y).mkQ.comp (P₁ H)) (by
    intro z hz
    exact (Submodule.Quotient.mk_eq_zero _).mpr (P₁_D₁ H hz))

@[simp] theorem normalizedPrism_mk {f g : C(X,Y)} (H : f.Homotopy g) (c : C₁ X) :
    normalizedPrism H ((D₁ X).mkQ c) = (D₂ Y).mkQ (P₁ H c) := rfl

theorem normalizedPrism_boundary {f g : C(X,Y)} (H : f.Homotopy g)
    {z : N₁ X} (hz : d₁ z = 0) : d₂ (normalizedPrism H z) = pushN₁ g z - pushN₁ f z := by
  obtain ⟨c,rfl⟩ := (D₁ X).mkQ_surjective z
  change b₁ c = 0 at hz
  have h := LinearMap.congr_fun (prism_boundary₁ H) c
  change b₂ (P₁ H c) + P₀ H (b₁ c) = push₁ g c - push₁ f c at h
  simp only [hz,map_zero,add_zero] at h
  change (D₁ Y).mkQ (b₂ (P₁ H c)) = _
  rw [h,map_sub]
  rfl

theorem normalizedPrism_support {f g : C(X,Y)} (H : f.Homotopy g)
    {U : Set X} {V : Set Y} (hH : ∀ t x, x ∈ U → H (t,x) ∈ V) :
    L₁ U ≤ (L₂ V).comap (normalizedPrism H) := by
  rw [L₁_span]
  apply Submodule.span_le.mpr
  rintro _ ⟨σ,hσ,rfl⟩
  change (D₂ Y).mkQ (P₁ H (Finsupp.single σ 1)) ∈ L₂ V
  rw [P₁_single]
  exact gen₂_mem (by rintro _ ⟨t,rfl⟩; exact hH t.1 (σ t.2) (hσ ⟨t.2,rfl⟩))

theorem homologyMap_homotopic {f g : C(X,Y)} (H : f.Homotopy g)
    {U : Set X} {V : Set Y} (hf : MapsTo f U V) (hg : MapsTo g U V)
    (hH : ∀ t x, x ∈ U → H (t,x) ∈ V) : homologyMap f hf = homologyMap g hg := by
  apply LinearMap.ext
  intro q
  obtain ⟨z,rfl⟩ := (boundaries U).mkQ_surjective q
  rw [homologyMap_mk,homologyMap_mk]
  apply eq_of_sub_eq_zero
  rw [← map_sub]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  refine ⟨-normalizedPrism H z.val,Submodule.neg_mem _ (normalizedPrism_support H hH z.property.1),?_⟩
  rw [map_neg,normalizedPrism_boundary H z.property.2]
  change -(pushN₁ g z.val - pushN₁ f z.val) = pushN₁ f z.val - pushN₁ g z.val
  abel

theorem homologyMap_id (U : Set X) : homologyMap (ContinuousMap.id X) (show MapsTo (ContinuousMap.id X) U U from fun _ h => h) = LinearMap.id := by
  apply LinearMap.ext
  intro q
  obtain ⟨z,rfl⟩ := (boundaries U).mkQ_surjective q
  rw [homologyMap_mk,LinearMap.id_apply]
  congr 1
  apply Subtype.ext
  exact pushN₁_id z.val

theorem homologyMap_comp (g : C(Y,Z)) (f : C(X,Y)) {U : Set X} {V : Set Y} {W : Set Z}
    (hf : MapsTo f U V) (hg : MapsTo g V W) :
    homologyMap (g.comp f) (hg.comp hf) = (homologyMap g hg).comp (homologyMap f hf) := by
  apply LinearMap.ext
  intro q
  obtain ⟨z,rfl⟩ := (boundaries U).mkQ_surjective q
  simp only [homologyMap_mk,LinearMap.comp_apply]
  congr 1
  apply Subtype.ext
  exact pushN₁_comp g f z.val

abbrev HomologyOne (X : Type*) [TopologicalSpace X] := Homology₁ (univ : Set X)
def homologyOneMap (f : C(X,Y)) : HomologyOne X →ₗ[ℤ] HomologyOne Y := homologyMap f (mapsTo_univ _ _)
@[simp] theorem homologyOneMap_id : homologyOneMap (ContinuousMap.id X) = LinearMap.id := homologyMap_id univ
@[simp] theorem homologyOneMap_comp (g : C(Y,Z)) (f : C(X,Y)) :
    homologyOneMap (g.comp f) = (homologyOneMap g).comp (homologyOneMap f) := homologyMap_comp g f _ _

theorem homologyOneMap_homotopic {f g : C(X,Y)} (H : f.Homotopy g) : homologyOneMap f = homologyOneMap g :=
  homologyMap_homotopic H _ _ (by intros; trivial)

/-- Actual homotopy equivalences induce integral cubical H1 isomorphisms. -/
def homologyOneEquiv (f : C(X,Y)) (g : C(Y,X))
    (Hgf : (g.comp f).Homotopy (ContinuousMap.id X))
    (Hfg : (f.comp g).Homotopy (ContinuousMap.id Y)) : HomologyOne X ≃ₗ[ℤ] HomologyOne Y :=
  LinearEquiv.ofLinearMap (homologyOneMap f) (homologyOneMap g)
    (by rw [← homologyOneMap_comp,homologyOneMap_homotopic Hfg,homologyOneMap_id])
    (by rw [← homologyOneMap_comp,homologyOneMap_homotopic Hgf,homologyOneMap_id])

end EilenbergGanea.CubicalSingular

namespace EilenbergGanea.CubicalSingular
open Set PathTransport
variable {X : Type*} [TopologicalSpace X]

abbrev PathChains (X : Type*) [TopologicalSpace X] := N₁ X ⧸ LinearMap.range (d₂ : N₂ X →ₗ[ℤ] N₁ X)
def chainClass : N₁ X →ₗ[ℤ] PathChains X := (LinearMap.range d₂).mkQ
def pathClass {x y : X} (p : Path x y) : PathChains X := chainClass (gen₁ p.toContinuousMap)

@[simp] theorem chainClass_boundary (b : N₂ X) : chainClass (d₂ b) = 0 :=
  (Submodule.Quotient.mk_eq_zero _).mpr ⟨b,rfl⟩
@[simp] theorem gen₁_const (x : X) : gen₁ (ContinuousMap.const I x) = 0 :=
  (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.subset_span ⟨x,rfl⟩)
@[simp] theorem pathClass_refl (x : X) : pathClass (Path.refl x) = 0 := by
  change chainClass (gen₁ (ContinuousMap.const I x)) = 0
  rw [gen₁_const,map_zero]

theorem chainClass_subdivision (z : N₁ X) : chainClass (SN₁ z) = chainClass z := by
  have h := chainClass_boundary (K₁ 1 z)
  rw [K₁_boundary] at h
  exact sub_eq_zero.mp (by simpa only [Function.iterate_one,map_sub] using h)

theorem pathClass_trans {x y z : X} (p : Path x y) (q : Path y z) :
    pathClass (p.trans q) = pathClass p + pathClass q := by
  rw [pathClass,← chainClass_subdivision]
  simp only [gen₁,SN₁_mk,S₁_single,Fintype.sum_bool,map_add,
    PathTransport.Local.cut_trans_left,PathTransport.Local.cut_trans_right]
  rw [add_comm]
  rfl

theorem pathClass_homotopy {x y : X} {p q : Path x y} (H : p.Homotopy q) :
    pathClass p = pathClass q := by
  have h := chainClass_boundary (gen₂ H.toHomotopy.toContinuousMap)
  have e₀ : edge₁ H.toHomotopy.toContinuousMap 0 = p.toContinuousMap := by ext t; simp [edge₁]
  have e₁ : edge₁ H.toHomotopy.toContinuousMap 1 = q.toContinuousMap := by ext t; simp [edge₁]
  have c₀ : edge₂ H.toHomotopy.toContinuousMap 0 = ContinuousMap.const I x := by ext t; simp [edge₂]
  have c₁ : edge₂ H.toHomotopy.toContinuousMap 1 = ContinuousMap.const I y := by ext t; simp [edge₂]
  change chainClass ((D₁ X).mkQ (b₂ (Finsupp.single H.toHomotopy.toContinuousMap 1))) = 0 at h
  simp only [b₂_single,one_smul,map_sub,map_add,e₀,e₁,c₀,c₁] at h
  change pathClass q - pathClass p - chainClass (gen₁ (ContinuousMap.const I y)) +
    chainClass (gen₁ (ContinuousMap.const I x)) = 0 at h
  have hh : pathClass q - pathClass p = 0 := by simpa only [gen₁_const,map_zero,sub_zero,add_zero] using h
  exact (sub_eq_zero.mp hh).symm

def quotientPathClass {x y : X} : PQ x y → PathChains X :=
  Quotient.lift (fun p => pathClass p) (fun _ _ ⟨H⟩ => pathClass_homotopy H)
@[simp] theorem quotientPathClass_mk {x y : X} (p : Path x y) :
    quotientPathClass (asClass p) = pathClass p := rfl
@[simp] theorem quotientPathClass_trans {x y z : X} (p : PQ x y) (q : PQ y z) :
    quotientPathClass (p.trans q) = quotientPathClass p + quotientPathClass q := by
  induction p using Quotient.inductionOn
  induction q using Quotient.inductionOn
  exact pathClass_trans _ _
@[simp] theorem quotientPathClass_refl (x : X) : quotientPathClass (Path.Homotopic.Quotient.refl x) = 0 :=
  pathClass_refl x
@[simp] theorem quotientPathClass_symm {x y : X} (p : PQ x y) :
    quotientPathClass p.symm = -quotientPathClass p := by
  have h := congrArg (quotientPathClass) (Path.Homotopic.Quotient.trans_symm p)
  rw [quotientPathClass_trans,quotientPathClass_refl] at h
  exact eq_neg_of_add_eq_zero_right h

def loopChainHom (r : X) : (FundamentalGroup X r)ᵐᵒᵖ →* Multiplicative (PathChains X) where
  toFun g := Multiplicative.ofAdd (quotientPathClass g.unop)
  map_one' := congrArg Multiplicative.ofAdd (quotientPathClass_refl r)
  map_mul' g h := congrArg Multiplicative.ofAdd (quotientPathClass_trans g.unop h.unop)

abbrev AbLoops (X : Type*) [TopologicalSpace X] (r : X) := Additive (Abelianization (FundamentalGroup X r)ᵐᵒᵖ)

def loopToChains (r : X) : AbLoops X r →ₗ[ℤ] PathChains X :=
  (Abelianization.lift (loopChainHom r)).toAdditive.toIntLinearMap

@[simp] theorem loopToChains_of (r : X) (g : (FundamentalGroup X r)ᵐᵒᵖ) :
    loopToChains r (Additive.ofMul (Abelianization.of g)) = quotientPathClass g.unop := rfl

def abHolonomy {r : X} (q : ∀ x, Path r x) (γ : Cube₁ X) : AbLoops X r :=
  Additive.ofMul (Abelianization.of (holonomy q γ))
@[simp] theorem abHolonomy_const {r : X} (q : ∀ x, Path r x) (x : X) :
    abHolonomy q (ContinuousMap.const I x) = 0 := by
  simp [abHolonomy]

def abHolonomyRaw {r : X} (q : ∀ x, Path r x) : C₁ X →ₗ[ℤ] AbLoops X r :=
  Finsupp.linearCombination ℤ (abHolonomy q)

def abHolonomyMap {r : X} (q : ∀ x, Path r x) : N₁ X →ₗ[ℤ] AbLoops X r :=
  (D₁ X).liftQ (abHolonomyRaw q) (by
    apply Submodule.span_le.mpr
    rintro _ ⟨x,rfl⟩
    simp [abHolonomyRaw,constant₁])

@[simp] theorem abHolonomyMap_gen {r : X} (q : ∀ x, Path r x) (γ : Cube₁ X) :
    abHolonomyMap q (gen₁ γ) = abHolonomy q γ := by simp [abHolonomyMap,gen₁,abHolonomyRaw]

theorem abHolonomy_square {r : X} (q : ∀ x, Path r x) (σ : Cube₂ X) :
    abHolonomy q (edge₂ σ 0) + abHolonomy q (edge₁ σ 1) =
      abHolonomy q (edge₁ σ 0) + abHolonomy q (edge₂ σ 1) := by
  have h := congrArg (fun g => Additive.ofMul (Abelianization.of g)) (holonomy_square q σ)
  simp only [map_mul] at h
  exact h

theorem abHolonomyMap_boundary {r : X} (q : ∀ x, Path r x) :
    (abHolonomyMap q).comp d₂ = 0 := by
  apply LinearMap.ext
  intro z
  obtain ⟨z,rfl⟩ := (D₂ X).mkQ_surjective z
  have he : (abHolonomyRaw q).comp b₂ = 0 := by
    apply Finsupp.lhom_ext
    intro σ a
    simp only [LinearMap.comp_apply,b₂_single,map_smul,map_sub,map_add,abHolonomyRaw,
      Finsupp.linearCombination_single,one_smul,LinearMap.zero_apply]
    have h := abHolonomy_square q σ
    have hz : abHolonomy q (edge₁ σ 1) - abHolonomy q (edge₁ σ 0) -
      abHolonomy q (edge₂ σ 1) + abHolonomy q (edge₂ σ 0) = 0 := by
      calc
        _ = (abHolonomy q (edge₂ σ 0) + abHolonomy q (edge₁ σ 1)) -
          (abHolonomy q (edge₁ σ 0) + abHolonomy q (edge₂ σ 1)) := by abel
        _ = 0 := by rw [h,sub_self]
    rw [hz,smul_zero]
  exact LinearMap.congr_fun he z

def chainsToLoops {r : X} (q : ∀ x, Path r x) : PathChains X →ₗ[ℤ] AbLoops X r :=
  (LinearMap.range d₂).liftQ (abHolonomyMap q) (by
    rintro _ ⟨z,rfl⟩
    exact LinearMap.congr_fun (abHolonomyMap_boundary q) z)
@[simp] theorem chainsToLoops_class {r : X} (q : ∀ x, Path r x) (z : N₁ X) :
    chainsToLoops q (chainClass z) = abHolonomyMap q z := rfl
@[simp] theorem chainsToLoops_path {r x y : X} (q : ∀ x, Path r x) (p : Path x y) :
    chainsToLoops q (pathClass p) = abHolonomy q p.toContinuousMap := abHolonomyMap_gen q _

end EilenbergGanea.CubicalSingular

namespace EilenbergGanea.CubicalSingular
open Set PathTransport
variable {X : Type*} [TopologicalSpace X]

@[simp] theorem quotientPathClass_based {r : X} (q : ∀ x, Path r x) {x y : X} (p : PQ x y) :
    quotientPathClass (based q p).unop = pathClass (q x) + quotientPathClass p - pathClass (q y) := by
  simp only [based,MulOpposite.unop_op,quotientPathClass_trans,quotientPathClass_symm,quotientPathClass_mk,sub_eq_add_neg]

def anchorChains {r : X} (q : ∀ x, Path r x) : C₀ X →ₗ[ℤ] PathChains X :=
  Finsupp.linearCombination ℤ (fun x => pathClass (q x))

theorem loopToChains_abHolonomy {r : X} (q : ∀ x, Path r x) (γ : Cube₁ X) :
    loopToChains r (abHolonomy q γ) = chainClass (gen₁ γ) - anchorChains q (d₁ (gen₁ γ)) := by
  change quotientPathClass (based q (asClass (cubePath γ))).unop = _
  rw [quotientPathClass_based,quotientPathClass_mk]
  simp only [gen₁,d₁_mk,b₁_single,one_smul,map_sub,anchorChains,Finsupp.linearCombination_single,one_smul]
  change pathClass (q (γ 0)) + pathClass (cubePath γ) - pathClass (q (γ 1)) =
    pathClass (cubePath γ) - (pathClass (q (γ 1)) - pathClass (q (γ 0)))
  abel

theorem loops_chains_identity {r : X} (q : ∀ x, Path r x) (z : N₁ X) :
    loopToChains r (abHolonomyMap q z) = chainClass z - anchorChains q (d₁ z) := by
  obtain ⟨c,rfl⟩ := (D₁ X).mkQ_surjective z
  have he : (loopToChains r).comp (abHolonomyRaw q) =
      chainClass.comp (D₁ X).mkQ - (anchorChains q).comp b₁ := by
    apply Finsupp.lhom_ext
    intro γ m
    change loopToChains r (abHolonomyRaw q (Finsupp.single γ m)) = _
    rw [← Finsupp.smul_single_one γ m]
    simp only [map_smul,LinearMap.sub_apply,LinearMap.comp_apply]
    rw [show abHolonomyRaw q (Finsupp.single γ 1) = abHolonomy q γ by simp [abHolonomyRaw],loopToChains_abHolonomy]
    simp only [smul_sub]
    rfl
  exact LinearMap.congr_fun he c

theorem ab_based_loop {r : X} (q : ∀ x, Path r x) (g : FundamentalGroup X r) :
    Abelianization.of (based q g) = Abelianization.of (MulOpposite.op g) := by
  let u : FundamentalGroup X r := asClass (q r)
  have he : based q g = (MulOpposite.op u : (FundamentalGroup X r)ᵐᵒᵖ) *
      MulOpposite.op g * (MulOpposite.op u)⁻¹ := rfl
  rw [he,map_mul,map_mul,map_inv]
  simp [mul_comm]

theorem chains_loops_identity {r : X} (q : ∀ x, Path r x) (g : AbLoops X r) :
    chainsToLoops q (loopToChains r g) = g := by
  revert g
  change ∀ g : Abelianization (FundamentalGroup X r)ᵐᵒᵖ,
    chainsToLoops q (loopToChains r (Additive.ofMul g)) = Additive.ofMul g
  intro g
  induction g using QuotientGroup.induction_on with
  | H g =>
    change chainsToLoops q (loopToChains r (Additive.ofMul (Abelianization.of g))) = Additive.ofMul (Abelianization.of g)
    rw [loopToChains_of]
    induction g using MulOpposite.rec' with
    | h g =>
      induction g using Quotient.inductionOn with
      | h p =>
        change chainsToLoops q (quotientPathClass (asClass p)) = Additive.ofMul ((Abelianization.of (G := (FundamentalGroup X r)ᵐᵒᵖ)) (MulOpposite.op (asClass p)))
        rw [quotientPathClass_mk,chainsToLoops_path]
        rw [abHolonomy,holonomy_path]
        change Additive.ofMul (Abelianization.of (based q (asClass p))) = _
        exact congrArg Additive.ofMul (ab_based_loop q (asClass p))

def homologyChainsMap : HomologyOne X →ₗ[ℤ] PathChains X :=
  (boundaries univ).liftQ (chainClass.comp (cyclesOn univ).subtype) (by
    rintro z ⟨b,_,he⟩
    change chainClass z.val = 0
    change d₂ b = z.val at he
    rw [← he,chainClass_boundary])
@[simp] theorem homologyChainsMap_mk (z : cyclesOn (univ : Set X)) :
    homologyChainsMap ((boundaries univ).mkQ z) = chainClass z.val := rfl

theorem homologyChainsMap_injective : Function.Injective (homologyChainsMap (X:=X)) := by
  apply LinearMap.ker_eq_bot.mp
  refine le_antisymm ?_ bot_le
  intro h hh
  obtain ⟨z,rfl⟩ := (boundaries univ).mkQ_surjective h
  change chainClass z.val = 0 at hh
  obtain ⟨b,hb⟩ := (Submodule.Quotient.mk_eq_zero (LinearMap.range d₂)).mp hh
  change (boundaries univ).mkQ z = 0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact ⟨b,by rw [L₂_univ]; trivial,hb⟩

def homologyToLoops {r : X} (q : ∀ x, Path r x) : HomologyOne X →ₗ[ℤ] AbLoops X r :=
  (chainsToLoops q).comp homologyChainsMap

theorem homologyToLoops_injective {r : X} (q : ∀ x, Path r x) : Function.Injective (homologyToLoops q) := by
  apply LinearMap.ker_eq_bot.mp
  refine le_antisymm ?_ bot_le
  intro h hh
  obtain ⟨z,rfl⟩ := (boundaries univ).mkQ_surjective h
  change abHolonomyMap q z.val = 0 at hh
  have hc := loops_chains_identity q z.val
  rw [z.property.2,map_zero,sub_zero,hh,map_zero] at hc
  apply homologyChainsMap_injective
  simpa only [homologyChainsMap_mk,map_zero] using hc.symm

theorem homologyToLoops_surjective {r : X} (q : ∀ x, Path r x) : Function.Surjective (homologyToLoops q) := by
  intro g
  have hg : ∃ w : (FundamentalGroup X r)ᵐᵒᵖ, Additive.ofMul (Abelianization.of w) = g := by
    exact QuotientGroup.mk'_surjective _ g
  obtain ⟨w,rfl⟩ := hg
  obtain ⟨p,hp⟩ := Quotient.exists_rep w.unop
  have hc : d₁ (gen₁ p.toContinuousMap) = 0 := by
    simp only [gen₁,d₁_mk,b₁_single,one_smul]
    change (Finsupp.single (p 1) (1:ℤ) - Finsupp.single (p 0) (1:ℤ)) = 0
    rw [p.target,p.source,sub_self]
  let z : cyclesOn (univ : Set X) := ⟨gen₁ p.toContinuousMap,by rw [L₁_univ]; trivial,hc⟩
  refine ⟨(boundaries univ).mkQ z,?_⟩
  change chainsToLoops q (pathClass p) = Additive.ofMul (Abelianization.of w)
  have he : loopToChains r (Additive.ofMul (Abelianization.of w)) = pathClass p := by
    rw [loopToChains_of]
    change quotientPathClass w.unop = quotientPathClass (asClass p)
    exact congrArg quotientPathClass hp.symm
  rw [← he,chains_loops_identity]

/-- Integral degree-one Hurewicz for actual paths, with no cellular hypothesis:
finite singular 1-cycles equal the abelianized topological fundamental group. -/
def hurewiczOne {r : X} (q : ∀ x, Path r x) : HomologyOne X ≃ₗ[ℤ] AbLoops X r :=
  LinearEquiv.ofBijective (homologyToLoops q)
    ⟨homologyToLoops_injective q,homologyToLoops_surjective q⟩

end EilenbergGanea.CubicalSingular


end

end OAI
