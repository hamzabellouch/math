import OAI.Geometry.Relativity.CKS.HeatTensor
import OAI.Geometry.Relativity.CKS.HeatGenerated

namespace OAI

noncomputable section
namespace CKSInducedSphere
noncomputable section
open Set Filter Finset
open scoped Topology ContDiff Manifold
open CKSSphericalHarmonics

lemma HeatGenerated.neg {p : ℕ → Poly} {F : ℝ → E → ℝ} (hF : HeatGenerated p F) :
    HeatGenerated p (fun t x => -F t x) := by
  simpa only [neg_one_mul] using HeatGenerated.coeff (fun _ => (-1:ℝ)) contDiffOn_const hF

lemma HeatGenerated.sub {p : ℕ → Poly} {F G : ℝ → E → ℝ}
    (hF : HeatGenerated p F) (hG : HeatGenerated p G) :
    HeatGenerated p (fun t x => F t x - G t x) := by
  simpa only [sub_eq_add_neg] using hF.add hG.neg

lemma HeatGenerated.joint_sphere_smooth {p : ℕ → Poly} (hp : PolynomialRapid p)
    {F : ℝ → E → ℝ} (hF : HeatGenerated p F) :
    ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × Sphere => F z.1 (z.2 : E)) := by
  have hmap : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 2)) 𝓘(ℝ, ℝ × E) ∞
      (fun z : ℝ × Sphere => (z.1, (z.2 : E))) :=
    contMDiff_fst.prodMk_space ((contMDiff_coe_sphere (n := 2)).comp contMDiff_snd)
  intro z
  exact ((hF.joint_smooth hp).contDiffAt
    (heatDomain_open.mem_nhds (sphere_ne_zero z.2))).comp_contMDiffAt hmap.contMDiffAt

lemma heatTensor_generated (p : ℕ → Poly) (hp : PolynomialRapid p) (i j : Ix) :
    HeatGenerated (inversePolynomials p) (fun t x => heatTensor p t x i j) := by
  have hi := inversePolynomials_rapid p hp
  have hH (a b : Ix) : HeatGenerated (inversePolynomials p)
      (fun t x => hess (spatialHeat (inversePolynomials p) (0,[]) t) x a b) :=
    ((HeatGenerated.basic (0,[]) (p := inversePolynomials p)).partial hi b).partial hi a
  change HeatGenerated _ (fun t x =>
    (∑ a, ∑ b, proj (fun c => x c) i a * hess (spatialHeat (inversePolynomials p) (0,[]) t) x a b * proj (fun c => x c) b j) -
    (∑ a, ∑ b, proj (fun c => x c) a b * hess (spatialHeat (inversePolynomials p) (0,[]) t) x a b) / 2 * proj (fun c => x c) i j)
  apply HeatGenerated.sub
  · apply HeatGenerated.congr (HeatGenerated.sum univ (fun a _ => HeatGenerated.sum univ (fun b _ =>
      HeatGenerated.coeff _ ((proj_smooth i a).mul (proj_smooth b j)) (hH a b))))
    intro t x hx
    apply sum_congr rfl
    intro a ha
    apply sum_congr rfl
    intro b hb
    ring
  · apply HeatGenerated.congr (HeatGenerated.coeff
      (fun x => proj (fun c => x c) i j / 2) ((proj_smooth i j).div_const 2)
      (HeatGenerated.sum univ (fun a _ => HeatGenerated.sum univ (fun b _ =>
        HeatGenerated.coeff _ (proj_smooth a b) (hH a b)))))
    intro t x hx
    ring

abbrev TensorFamily (r : ℕ) := (Fin r → Ix) → ℝ → E → ℝ

def scalarTensor (F : ℝ → E → ℝ) : TensorFamily 0 := fun _ => F

def matrixTensor (F : ℝ → E → Mat) : TensorFamily 2 := fun a t x => F t x (a 0) (a 1)

def covariantD {r : ℕ} (T : TensorFamily r) : TensorFamily (r+1) :=
  fun a t x => ∑ k : Ix, ∑ b : Fin r → Ix,
    (proj (fun i => x i) (a 0) k * ∏ m : Fin r, proj (fun i => x i) (a m.succ) (b m)) *
      pd k (fun y => T b t y) x

def covariantIterate {r : ℕ} (T : TensorFamily r) : (a : ℕ) → TensorFamily (r+a)
  | 0 => T
  | a+1 => covariantD (covariantIterate T a)

def timeIterate (F : ℝ → E → ℝ) : ℕ → ℝ → E → ℝ
  | 0 => F
  | b+1 => td (timeIterate F b)

def covariantTimeJet {r : ℕ} (T : TensorFamily r) (a b : ℕ) : TensorFamily (r+a) :=
  covariantIterate (fun c => timeIterate (T c) b) a

lemma covariantD_generated {p : ℕ → Poly} (hp : PolynomialRapid p)
    {r : ℕ} {T : TensorFamily r} (hT : ∀ c, HeatGenerated p (T c))
    (a : Fin (r+1) → Ix) : HeatGenerated p (covariantD T a) := by
  unfold covariantD
  apply HeatGenerated.sum univ
  intro k hk
  apply HeatGenerated.sum univ
  intro b hb
  apply HeatGenerated.coeff
  · exact (proj_smooth (a 0) k).mul (contDiffOn_prod (fun m _ => proj_smooth (a m.succ) (b m)))
  · exact (hT b).partial hp k

lemma covariantIterate_generated {p : ℕ → Poly} (hp : PolynomialRapid p)
    {r : ℕ} {T : TensorFamily r} (hT : ∀ c, HeatGenerated p (T c))
    (a : ℕ) (c : Fin (r+a) → Ix) : HeatGenerated p (covariantIterate T a c) := by
  induction a with
  | zero => exact hT c
  | succ a ih => exact covariantD_generated hp ih c

lemma timeIterate_generated {p : ℕ → Poly} (hp : PolynomialRapid p)
    {F : ℝ → E → ℝ} (hF : HeatGenerated p F) (b : ℕ) :
    HeatGenerated p (timeIterate F b) := by
  induction b with
  | zero => exact hF
  | succ b ih => exact ih.time hp

lemma covariantTimeJet_generated {p : ℕ → Poly} (hp : PolynomialRapid p)
    {r : ℕ} {T : TensorFamily r} (hT : ∀ c, HeatGenerated p (T c))
    (a b : ℕ) (c : Fin (r+a) → Ix) : HeatGenerated p (covariantTimeJet T a b c) :=
  covariantIterate_generated hp (fun d => timeIterate_generated hp (hT d) b) a c

def tensorNorm {r : ℕ} (T : TensorFamily r) (t : ℝ) (x : E) : ℝ :=
  ‖(WithLp.toLp 2 (fun c : Fin r → Ix => T c t x) : EuclideanSpace ℝ (Fin r → Ix))‖

lemma euclidean_norm_le_sum_norm {J : Type*} [Fintype J] (v : J → ℝ) :
    ‖(WithLp.toLp 2 v : EuclideanSpace ℝ J)‖ ≤ ∑ j, ‖v j‖ := by
  classical
  have he : (WithLp.toLp 2 v : EuclideanSpace ℝ J) =
      ∑ j, (WithLp.toLp 2 (Pi.single j (v j)) : EuclideanSpace ℝ J) := by
    ext k
    simp
  rw [he]
  exact (norm_sum_le _ _).trans_eq (by simp only [PiLp.toLp_single, PiLp.norm_single])

lemma generated_tensor_decay {p : ℕ → Poly} (hp : PolynomialRapid p)
    {r : ℕ} {T : TensorFamily r} (hT : ∀ c, HeatGenerated p (T c)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → ∀ x : E, ‖x‖ = 1 →
      tensorNorm T t x ≤ C * Real.exp (-6 * t) := by
  choose C hC hb using fun c => (hT c).decay hp
  refine ⟨∑ c, C c, sum_nonneg (fun c _ => hC c), fun t ht x hx => ?_⟩
  exact (euclidean_norm_le_sum_norm _).trans (by
    rw [sum_mul]
    exact sum_le_sum (fun c _ => hb c t ht x hx))

theorem heat_covariant_estimates (p : ℕ → Poly) (hp : PolynomialRapid p) (a b : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → ∀ x : E, ‖x‖ = 1 →
      tensorNorm (covariantTimeJet (scalarTensor (spatialHeat p (0,[]))) a b) t x +
      tensorNorm (covariantTimeJet (matrixTensor (heatTensor p)) a b) t x ≤
        C * Real.exp (-6*t) := by
  obtain ⟨C, hC, hCb⟩ := generated_tensor_decay hp
    (covariantTimeJet_generated hp (r := 0) (T := scalarTensor (spatialHeat p (0,[])))
      (fun _ => HeatGenerated.basic (0,[])) a b)
  obtain ⟨D, hD, hDb⟩ := generated_tensor_decay (inversePolynomials_rapid p hp)
    (covariantTimeJet_generated (inversePolynomials_rapid p hp)
      (r := 2) (T := matrixTensor (heatTensor p)) (fun c => heatTensor_generated p hp (c 0) (c 1)) a b)
  exact ⟨C+D, add_nonneg hC hD, fun t ht x hx => by
    simpa only [add_mul] using add_le_add (hCb t ht x hx) (hDb t ht x hx)⟩

end
end CKSInducedSphere

end

end OAI
