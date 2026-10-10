import OAI.MathematicalPhysics.AlternatingFlow.JetPrograms

namespace OAI

section FieldProgramsDevelopment

open scoped BigOperators Topology ContDiff
namespace AlternatingNS.Effective
attribute [local instance] Arithmetic.rationalCoding

variable {A E F : Type*} [Primcodable A]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

def JetBound (f : A → E → F) : Prop :=
  (∀ a, ContDiff ℝ ∞ (f a)) ∧ ∃ B : A × ℕ → ℕ, Computable B ∧
    ∀ a r x, ‖iteratedFDeriv ℝ r (f a) x‖ ≤ B (a,r)

lemma Certified.jetBound {f : A → ℝ × Space → F} (hf : Certified f) : JetBound f := by
  obtain ⟨sf,B,hB,h⟩ := hf
  exact ⟨sf, fun z => B (z.1,0,z.2), hB.comp (Computable.fst.pair ((Computable.const 0).pair Computable.snd)),
    fun a r z => by simpa using h a 0 r z⟩

lemma JetBound.congr {f g : A → E → F} (hf : JetBound f) (h : ∀ a x, f a x = g a x) : JetBound g := by
  rwa [← funext (fun a => funext (h a))]

lemma JetBound.param {B : Type*} [Primcodable B] {f : A → E → F} (hf : JetBound f)
    {g : B → A} (hg : Computable g) : JetBound (fun b => f (g b)) := by
  obtain ⟨sf,C,hC,h⟩ := hf
  exact ⟨fun b => sf (g b), fun z => C (g z.1,z.2), hC.comp ((hg.comp Computable.fst).pair Computable.snd), fun b => h (g b)⟩

lemma JetBound.comp_unit {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : A → E → F} (hf : JetBound f) (L : A → G →L[ℝ] E) (hL : ∀ a, ‖L a‖ ≤ 1) :
    JetBound (fun a => f a ∘ L a) := by
  obtain ⟨sf,B,hB,h⟩ := hf
  refine ⟨fun a => (sf a).comp (L a).contDiff, B, hB, fun a r z => ?_⟩
  exact (Bounds.norm_comp_linear (f a) (sf a) (L a) r z).trans
    ((mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) (hL a))).trans (h a r _))

lemma JetBound.linear_unit {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : A → E → F} (hf : JetBound f) (L : A → F →L[ℝ] G) (hL : ∀ a, ‖L a‖ ≤ 1) :
    JetBound (fun a => L a ∘ f a) := by
  obtain ⟨sf,B,hB,h⟩ := hf
  refine ⟨fun a => (L a).contDiff.comp (sf a), B, hB, fun a r z => ?_⟩
  exact (Bounds.norm_postcomp_linear (f a) (sf a) (L a) r z).trans
    ((mul_le_of_le_one_left (norm_nonneg _) (hL a)).trans (h a r z))

lemma Scaled.jetBound {s : A → ℕ → ℝ} {f : A → ℕ → E → F} (hf : Scaled s f)
    (hs : ∀ a n, 0 ≤ s a n) (S : A × ℕ → ℕ) (hS : Computable S)
    (sS : ∀ a n, s a n ≤ S (a,n)) : JetBound (fun a : A × ℕ => f a.1 a.2) := by
  obtain ⟨sf,B,hB,h⟩ := hf
  refine ⟨fun a => sf a.1 a.2, fun z => B (z.1.1,z.2) * S z.1 ^ z.2,
    Primrec.nat_mul.to_comp.comp
      (hB.comp ((Computable.fst.comp Computable.fst).pair Computable.snd))
      (nat_pow.to_comp.comp (hS.comp Computable.fst) Computable.snd), ?_⟩
  rintro ⟨a,n⟩ r x
  simpa only [Nat.cast_mul, Nat.cast_pow] using (h a r n x).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hs a n) (sS a n) r) (Nat.cast_nonneg _))

lemma norm_proj (i : Fin 3) : ‖PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by simpa using PiLp.norm_apply_le x i)

lemma norm_fst : ‖ContinuousLinearMap.fst ℝ ℝ Space‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by simpa using norm_fst_le x)

lemma norm_snd : ‖ContinuousLinearMap.snd ℝ ℝ Space‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by simpa using norm_snd_le x)

lemma JetBound.named_wordJet {f : A → ℝ × Space → ℝ} (hf : JetBound f)
    (hn : Named (fun z : A × RationalPoint => f z.1 (rationalPoint z.2))) :
    Named (fun z : (A × List (Fin 4)) × RationalPoint => wordJet (f z.1.1) z.1.2 (rationalPoint z.2)) := by
  obtain ⟨sf,B,hB,h⟩ := hf
  exact AlternatingNS.Effective.named_wordJet sf hn B hB h

lemma JetBound.named_directional {f : A → ℝ × Space → ℝ} (hf : JetBound f)
    (hn : Named (fun z : A × RationalPoint => f z.1 (rationalPoint z.2)))
    (i : A → Fin 4) (hi : Computable i) :
    Named (fun z : A × RationalPoint => fderiv ℝ (f z.1) (rationalPoint z.2) (direction (i z.1))) := by
  have hw : Computable (fun z : A × RationalPoint => ((z.1,[i z.1]),z.2)) :=
    (Computable.fst.pair (Primrec.list_cons.to_comp.comp (hi.comp Computable.fst) (Computable.const []))).pair Computable.snd
  have hh := hf.named_wordJet hn |>.comp hw
  exact hh.congr (fun _ => rfl)

lemma Certified.sum3 {f : Fin 3 → A → ℝ × Space → F} (hf : ∀ i, Certified (f i)) :
    Certified (fun a z => ∑ i : Fin 3, f i a z) := by
  exact ((hf 0).add ((hf 1).add (hf 2))).congr (fun _ _ => by simp [Fin.sum_univ_succ])

lemma Certified.dx {f : A → Velocity} (hf : Certified (fun a => Function.uncurry (f a))) (i : Fin 3) :
    Certified (fun a => Function.uncurry (dx i (f a))) :=
  (hf.directional (fun _ => (0,e i)) (fun _ => by simp [Prod.norm_def, Bounds.norm_e])).congr
    (fun a z => (Bounds.dx_eq_full_directional (f a) (hf.1 a) i z).symm)

lemma Certified.fullDt {f : A → Velocity} (hf : Certified (fun a => Function.uncurry (f a))) :
    Certified (fun a => Function.uncurry (Analytic.fullDt (f a))) :=
  (hf.directional (fun _ => (1,0)) (fun _ => by simp [Prod.norm_def])).congr
    (fun a z => (Bounds.fullDt_eq_full_directional (f a) (hf.1 a) z).symm)

lemma Certified.component {f : A → ℝ × Space → Space} (hf : Certified f) (i : A → Fin 3) :
    Certified (fun a z => f a z (i a)) :=
  hf.linear (fun a => PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) (i a)) (fun _ => 1) (Computable.const 1) (fun a => by simpa using norm_proj (i a))

lemma Certified.advection {f : A → Velocity} (hf : Certified (fun a => Function.uncurry (f a))) :
    Certified (fun a => Function.uncurry (advection (f a))) := by
  have hi (i : Fin 3) := (hf.component (fun _ => i)).smul (hf.dx i)
  exact (Certified.sum3 hi).congr (fun a z => (Bounds.advection_eq_sum (f a) z.1 z.2).symm)

lemma Certified.laplacian {f : A → Velocity} (hf : Certified (fun a => Function.uncurry (f a))) :
    Certified (fun a => Function.uncurry (laplacian (f a))) := Certified.sum3 (fun i => (hf.dx i).dx i)

noncomputable def fullForce (ν : ℝ) (M : Machine) (w : List ℕ) : Velocity :=
  fun t x => Analytic.fullDt (Construction.velocity M w) t x + advection (Construction.velocity M w) t x -
    ν • laplacian (Construction.velocity M w) t x

lemma force_certified (ν : ℝ) : Certified (fun z : Machine × List ℕ => Function.uncurry (fullForce ν z.1 z.2)) := by
  obtain ⟨D,hD⟩ := exists_nat_ge |ν|
  exact (velocity_certified.fullDt.add velocity_certified.advection).sub (velocity_certified.laplacian.csmul ν D hD)

lemma fullForce_half (ν : ℝ) (M : Machine) (w : List ℕ) :
    Bounds.HalfEq (fullForce ν M w) (Construction.force ν M w) := by
  intro t ht x
  simp only [fullForce, Construction.force, residual]
  rw [Analytic.dt_eq_full _ (Construction.velocity_smooth M w) t ht x]

end AlternatingNS.Effective

end FieldProgramsDevelopment

end OAI
