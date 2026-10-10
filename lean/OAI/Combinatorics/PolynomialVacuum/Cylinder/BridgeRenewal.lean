import OAI.Combinatorics.PolynomialVacuum.Bridge.BridgePrimitiveMass
import OAI.Combinatorics.PolynomialVacuum.Bridge.PrimitiveCounterexample

namespace OAI

namespace PolynomialVacuumBridge.Corridor.BridgeWord
open PolynomialVacuumCylinder
variable {M : ℕ}

def shiftCylinderVertex (M : ℕ) (x y : ℤ) : PolynomialVacuumCylinder.Vertex M → PolynomialVacuumCylinder.Vertex M
  | .up i j => .up (i+(x : ZMod M)) (j+y)
  | .down i j => .down (i+(x : ZMod M)) (j+y)

theorem project_shiftVertex (x y : ℤ) (v : PolynomialVacuumBridge.Corridor.Vertex) :
    projectVertex M (shiftVertex x y v)=shiftCylinderVertex M x y (projectVertex M v) := by
  cases v <;> simp [projectVertex,shiftVertex,shiftCylinderVertex]

theorem shiftCylinderVertex_injective (x y : ℤ) : Function.Injective (shiftCylinderVertex M x y) := by
  intro v u h
  cases v <;> cases u <;> simp_all [shiftCylinderVertex]

@[simp] theorem cylinderSafe_mul (A B : BridgeWord) :
    CylinderSafe M (A*B) ↔ CylinderSafe M A ∧ CylinderSafe M B := by
  unfold CylinderSafe
  simp only [word_mul,PolynomialVacuumBridge.Corridor.traced_append,A.terminal_source,← shift_traced,
    List.map_append,List.map_map,Function.comp_def,project_shiftVertex]
  rw [show List.map (fun x => shiftCylinderVertex M A.endX (A.height : ℤ) (projectVertex M x))
      (traced bottomSource B.word) = List.map (shiftCylinderVertex M A.endX (A.height : ℤ))
      (List.map (projectVertex M) (traced bottomSource B.word)) from (List.map_map (g := shiftCylinderVertex M A.endX (A.height : ℤ))
        (f := projectVertex M) (l := traced bottomSource B.word)).symm]
  rw [List.nodup_append]
  rw [List.nodup_map_iff (shiftCylinderVertex_injective _ _)]
  constructor
  · intro h; exact ⟨h.1,h.2.1⟩
  · rintro ⟨ha,hb⟩
    refine ⟨ha,hb,?_⟩
    intro v hv u hu he
    obtain ⟨v',hv',rfl⟩ := List.mem_map.mp hv
    obtain ⟨u',hu',rfl⟩ := List.mem_map.mp hu
    obtain ⟨u'',hu'',rfl⟩ := List.mem_map.mp hu'
    have hA := (A.inStrip v' hv').2
    have hB := (B.inStrip u'' hu'').1
    have hj := congrArg (fun v : PolynomialVacuumCylinder.Vertex M => match v with | .up _ j => j | .down _ j => j) he
    cases v' <;> cases u'' <;> simp only [projectVertex,shiftCylinderVertex] at hj
    all_goals simp only [layer] at hA hB; omega

noncomputable def renewalRatio (M : ℕ) : ℝ := 1-mass (zigzag M)

theorem renewalRatio_nonneg (M : ℕ) : 0≤renewalRatio M := by
  have := primitive_finite_sum_le_one {zigzag M} (by simp [zigzag_primitive])
  simp only [Finset.sum_singleton] at this
  exact sub_nonneg.mpr this

theorem renewalRatio_lt_one (M : ℕ) : renewalRatio M<1 := by
  unfold renewalRatio
  linarith [mass_pos (zigzag M)]

theorem safe_primitive_finite_sum_bound (M : ℕ) (hM : 0<M) (S : Finset BridgeWord)
    (hS : ∀ A∈S,A.IsPrimitive ∧ CylinderSafe M A) :
    (∑ A∈S,mass A)≤renewalRatio M := by
  classical
  have hz : zigzag M∉S := fun hz => zigzag_unsafe M hM (hS _ hz).2
  have hb := primitive_finite_sum_le_one (insert (zigzag M) S) (by
    intro A hA
    rcases Finset.mem_insert.mp hA with rfl | hA
    · exact zigzag_primitive M
    · exact (hS A hA).1)
  rw [Finset.sum_insert hz] at hb
  unfold renewalRatio
  linarith

noncomputable def factors (A : BridgeWord) : List BridgeWord := (exists_primitive_factors A).choose

theorem factors_primitive (A : BridgeWord) : ∀ B∈factors A,B.IsPrimitive :=
  (exists_primitive_factors A).choose_spec.1
@[simp] theorem factors_prod (A : BridgeWord) : (factors A).prod=A :=
  (exists_primitive_factors A).choose_spec.2

theorem factors_safe (A : BridgeWord) (hA : CylinderSafe M A) : ∀ B∈factors A,CylinderSafe M B := by
  have hp : CylinderSafe M (factors A).prod := by simpa using hA
  generalize factors A=L at hp ⊢
  induction L with
  | nil => simp
  | cons C L ih =>
    rw [List.prod_cons,cylinderSafe_mul] at hp
    intro B hB
    rcases List.mem_cons.mp hB with rfl | hB
    · exact hp.1
    · exact ih hp.2 B hB

theorem mem_sequences_iff (S : Finset BridgeWord) (k : ℕ) (L : List BridgeWord) :
    L∈sequences S k ↔ L.length=k ∧ ∀ A∈L,A∈S := by
  classical
  induction k generalizing L with
  | zero => cases L <;> simp [sequences]
  | succ k ih =>
    cases L with
    | nil => simp [sequences]
    | cons A L =>
      constructor
      · intro h
        obtain ⟨⟨B,K⟩,hp,he⟩ := Finset.mem_image.mp h
        obtain ⟨rfl,rfl⟩ := List.cons.inj he
        obtain ⟨ha,hL⟩ := Finset.mem_product.mp hp
        obtain ⟨hk,hm⟩ := (ih K).mp hL
        exact ⟨by simp [hk],by simpa using And.intro ha hm⟩
      · rintro ⟨hk,hm⟩
        apply Finset.mem_image.mpr
        refine ⟨(A,L),Finset.mem_product.mpr ⟨hm A (by simp),?_⟩,rfl⟩
        exact (ih L).mpr ⟨by simpa using hk,fun B hB => hm B (List.mem_cons_of_mem A hB)⟩

end PolynomialVacuumBridge.Corridor.BridgeWord

end OAI
