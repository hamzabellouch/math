import OAI.Geometry.SingularHomology.SimplexCoordinates
import OAI.Dynamics.EntropyCounterexample.Definitions

namespace OAI

noncomputable section

namespace Problem340.SingularSimplexCircleLift

abbrev Circle := AddCircle (1 : ℝ)
abbrev Simplex (n : ℕ) := Convexity.StdSimplex ℝ (Fin (n + 1))

theorem exists_lift (n : ℕ) (σ : C(Simplex n, Circle)) :
    ∃ F : C(Simplex n, ℝ), ∀ x, (F x : Circle) = σ x := by
  let : ContractibleSpace (Simplex n) :=
    RealSimplex.contractible
  let : LocallyPathConnectedSpace (Simplex n) :=
    RealSimplex.locallyPathConnected
  let x : Simplex n := Convexity.StdSimplex.single 0
  obtain ⟨y, hy⟩ := QuotientAddGroup.mk_surjective (σ x)
  obtain ⟨F, hF, -⟩ := (AddCircle.isCoveringMap_coe (1 : ℝ)).existsUnique_continuousMap_lifts
    σ x y hy
  exact ⟨F, fun z => congrFun hF.2 z⟩

theorem sub_eq_sub_of_lifts {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    (F G : C(X, ℝ)) (h : ∀ x, (F x : Circle) = (G x : Circle)) (x y : X) :
    F x - F y = G x - G y := by
  have hc : ∀ z : X, ((F z - G z : ℝ) : Circle) = 0 := by
    intro z
    rw [AddCircle.coe_sub, h z, sub_self]
  have he := (AddCircle.isCoveringMap_coe (1 : ℝ)).const_of_comp
    (F.continuous.sub G.continuous) (fun a b => (hc a).trans (hc b).symm) x y
  change F x - G x = F y - G y at he
  linarith

def lift {n : ℕ} (σ : C(Simplex n, Circle)) : C(Simplex n, ℝ) :=
  Classical.choose (exists_lift n σ)

@[simp] theorem coe_lift {n : ℕ} (σ : C(Simplex n, Circle)) (x : Simplex n) :
    (lift σ x : Circle) = σ x :=
  Classical.choose_spec (exists_lift n σ) x

def increment {n : ℕ} (σ : C(Simplex n, Circle)) (x y : Simplex n) : ℝ :=
  lift σ y - lift σ x

theorem increment_eq {n : ℕ} (σ : C(Simplex n, Circle))
    (F : C(Simplex n, ℝ)) (hF : ∀ x, (F x : Circle) = σ x) (x y : Simplex n) :
    increment σ x y = F y - F x := by
  apply sub_eq_sub_of_lifts
  intro z
  exact (coe_lift σ z).trans (hF z).symm

theorem increment_comp {n m : ℕ} (σ : C(Simplex n, Circle))
    (φ : C(Simplex m, Simplex n)) (x y : Simplex m) :
    increment (σ.comp φ) x y = increment σ (φ x) (φ y) := by
  exact increment_eq (σ.comp φ) ((lift σ).comp φ)
    (fun z => coe_lift σ (φ z)) x y

@[simp] theorem increment_self {n : ℕ} (σ : C(Simplex n, Circle)) (x : Simplex n) :
    increment σ x x = 0 := sub_self _

theorem increment_reverse {n : ℕ} (σ : C(Simplex n, Circle)) (x y : Simplex n) :
    increment σ y x = -increment σ x y := by
  simp only [increment, neg_sub]

theorem increment_add {n : ℕ} (σ : C(Simplex n, Circle)) (x y z : Simplex n) :
    increment σ x y + increment σ y z = increment σ x z := by
  dsimp [increment]
  ring

theorem increment_map {n m : ℕ} (σ : C(Simplex n, Circle))
    (f : Fin (m + 1) → Fin (n + 1)) (x y : Simplex m) :
    increment (σ.comp ⟨Convexity.StdSimplex.map f, Convexity.StdSimplex.continuous_map ℝ f⟩) x y =
      increment σ (Convexity.StdSimplex.map f x) (Convexity.StdSimplex.map f y) :=
  increment_comp σ _ x y

theorem increment_map_vertices {n m : ℕ} (σ : C(Simplex n, Circle))
    (f : Fin (m + 1) → Fin (n + 1)) (i j : Fin (m + 1)) :
    increment (σ.comp ⟨Convexity.StdSimplex.map f, Convexity.StdSimplex.continuous_map ℝ f⟩)
      (Convexity.StdSimplex.single i) (Convexity.StdSimplex.single j) =
      increment σ (Convexity.StdSimplex.single (f i)) (Convexity.StdSimplex.single (f j)) := by
  rw [increment_map, Convexity.StdSimplex.map_single, Convexity.StdSimplex.map_single]

theorem increment_triangle (σ : C(Simplex 2, Circle)) :
    increment σ (Convexity.StdSimplex.single 1) (Convexity.StdSimplex.single 2) -
      increment σ (Convexity.StdSimplex.single 0) (Convexity.StdSimplex.single 2) +
      increment σ (Convexity.StdSimplex.single 0) (Convexity.StdSimplex.single 1) = 0 := by
  dsimp [increment]
  ring

end Problem340.SingularSimplexCircleLift

end

end OAI
