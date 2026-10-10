import OAI.GroupTheory.PolycyclicRecognition.Algebra.CentralCommutatorPowers

namespace OAI

/-! # Collecting a word across a generator modulo a central subgroup -/

namespace PolycyclicRecognition
open scoped commutatorElement

variable {A G : Type*} [CommGroup A] [Group G]

theorem central_word_collection {I : Type*} (z : A →* G)
    (hz : ∀ a, z a ∈ Subgroup.center G) (l : List I) (f : I → G) (b : G) (c : I → A)
    (hc : ∀ i ∈ l, f i * b = z (c i) * b * f i) :
    (l.map f).prod * b = z ((l.map c).prod) * b * (l.map f).prod := by
  induction l with
  | nil => simp
  | cons i l ih =>
    have hi := hc i (List.mem_cons_self ..)
    have hl := ih (fun j hj => hc j (List.mem_cons_of_mem i hj))
    have hc' : f i * z ((l.map c).prod) = z ((l.map c).prod) * f i :=
      Subgroup.mem_center_iff.mp (hz _) (f i)
    simp only [List.prod_cons, List.map_cons, map_mul]
    calc
      (f i * (l.map f).prod) * b = f i * ((l.map f).prod * b) := mul_assoc ..
      _ = f i * (z ((l.map c).prod) * b * (l.map f).prod) := by rw [hl]
      _ = z ((l.map c).prod) * (f i * b) * (l.map f).prod := by
        rw [← mul_assoc, ← mul_assoc, hc']
        simp only [mul_assoc]
      _ = z ((l.map c).prod) * (z (c i) * b * f i) * (l.map f).prod := by rw [hi]
      _ = (z (c i) * z ((l.map c).prod)) * b * (f i * (l.map f).prod) := by
        have hcomm : z ((l.map c).prod) * z (c i) = z (c i) * z ((l.map c).prod) := by
          rw [← map_mul, mul_comm, map_mul]
        simp only [← mul_assoc]
        rw [hcomm]

theorem central_word_powers_collection {I : Type*} (z : A →* G)
    (hz : ∀ a, z a ∈ Subgroup.center G) (l : List I) (f : I → G) (b : G)
    (c : I → A) (hc : ∀ i ∈ l, ⁅f i, b⁆ = z (c i)) (u : I → ℤ) (n : ℤ) :
    (l.map (fun i => f i ^ u i)).prod * b ^ n =
      z ((l.map (fun i => c i ^ (u i * n))).prod) * b ^ n *
        (l.map (fun i => f i ^ u i)).prod := by
  apply central_word_collection z hz
  intro i hi
  have hcentral : ⁅f i, b⁆ ∈ Subgroup.center G := by rw [hc i hi]; exact hz _
  simpa only [hc i hi, map_zpow] using central_zpow_collection hcentral (u i) n

end PolycyclicRecognition

end OAI
