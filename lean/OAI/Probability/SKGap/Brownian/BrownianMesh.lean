import Mathlib
import OAI.Probability.SKGap.Brownian.BrownianCoordinateTail
import OAI.Probability.SKGap.Stability.GaugeStabilityLaw
import OAI.Probability.SKGap.Stability.RootFieldTransfer

namespace OAI

section

noncomputable section
namespace SKGap.ObservationBridge
open MeasureTheory ProbabilityTheory Real Set SKGap.PathBridge
open scoped BigOperators ENNReal NNReal Topology
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0→Ω→ℝ}

def observationField {n : ℕ} (B : ℝ≥0→Ω→ℝ) (σ : Spin n) (t : ℝ≥0)
    (ω : Fin n→Ω) : Field n := fun i=>(t:ℝ)*spinValue (σ i)+B t (ω i)

def meshModulusBad (B : ℝ≥0→Ω→ℝ) (m : ℕ) (δ : ℝ≥0) (κ : ℝ) (n : ℕ) :
    Set (Fin n→Ω) :=
  {ω | ∃ k : Fin m,∃ u : UnitInterval,
    κ^2*(n:ℝ) < ∑ i,(B ((k:ℝ≥0)*δ+δ*⟨u.1,u.2.1⟩) (ω i)-B ((k:ℝ≥0)*δ) (ω i))^2}

lemma meshModulusBad_measure (hB : IsBrownianReal B P) {κ : ℝ} (hκ : 0<κ) :
    ∃ δ₀ : ℝ, 0<δ₀ ∧ ∀ m : ℕ,∀ δ : ℝ≥0,0<δ → (δ:ℝ)≤δ₀ → ∀ n,
      (Measure.pi (fun _ : Fin n=>P)).real (meshModulusBad B m δ κ n) ≤
        (m:ℝ)*exp (-(n:ℝ)) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨δ₀,hδ₀,ht⟩ := brownian_coordinate_modulus_small hB hκ
  refine ⟨δ₀,hδ₀,fun m δ hδ hδle n=>?_⟩
  have he : meshModulusBad B m δ κ n = ⋃ k : Fin m,
      {ω | ∃ u : UnitInterval,
        κ^2*(n:ℝ) < ∑ i,(B ((k:ℝ≥0)*δ+δ*⟨u.1,u.2.1⟩) (ω i)-B ((k:ℝ≥0)*δ) (ω i))^2} := by
    ext ω;simp [meshModulusBad]
  rw [he]
  calc
    _ ≤ ∑ k : Fin m,(Measure.pi (fun _ : Fin n=>P)).real
      {ω | ∃ u : UnitInterval,
        κ^2*(n:ℝ) < ∑ i,(B ((k:ℝ≥0)*δ+δ*⟨u.1,u.2.1⟩) (ω i)-B ((k:ℝ≥0)*δ) (ω i))^2} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _k : Fin m,exp (-(n:ℝ)) := Finset.sum_le_sum (fun k _=>ht ((k:ℝ≥0)*δ) δ hδ hδle n)
    _ = _ := by simp

omit [MeasurableSpace Ω] in
lemma observationField_increment {n : ℕ} (σ : Spin n) (s δ : ℝ≥0) (u : UnitInterval)
    (ω : Fin n→Ω) {κ : ℝ} (hκ : 0≤κ)
    (hb : ∑ i,(B (s+δ*⟨u.1,u.2.1⟩) (ω i)-B s (ω i))^2 ≤ κ^2*(n:ℝ)) :
    vectorNorm (observationField B σ (s+δ*⟨u.1,u.2.1⟩) ω-observationField B σ s ω) ≤
      ((δ:ℝ)+κ)*sqrt (n:ℝ) := by
  let d : Field n := fun i=>(δ:ℝ)*u.1*spinValue (σ i)
  let b : Field n := fun i=>B (s+δ*⟨u.1,u.2.1⟩) (ω i)-B s (ω i)
  have he : observationField B σ (s+δ*⟨u.1,u.2.1⟩) ω-observationField B σ s ω=d+b := by
    ext i
    simp only [observationField,Pi.sub_apply,Pi.add_apply,NNReal.coe_add,d,b]
    change ((s:ℝ)+(δ:ℝ)*u.1)*spinValue (σ i)+B (s+δ*⟨u.1,u.2.1⟩) (ω i) -
      ((s:ℝ)*spinValue (σ i)+B s (ω i))=
      (δ:ℝ)*u.1*spinValue (σ i)+(B (s+δ*⟨u.1,u.2.1⟩) (ω i)-B s (ω i))
    ring
  have hd : vectorNorm d ≤ (δ:ℝ)*sqrt (n:ℝ) := by
    apply vectorNorm_le_of_sq_sum (by positivity)
    simp only [d,mul_pow,spinValue_sq,mul_one,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    rw [sq_sqrt (Nat.cast_nonneg n)]
    have hu : u.1^2≤1 := by nlinarith [mul_le_mul_of_nonneg_left u.2.2 u.2.1]
    nlinarith [mul_nonneg (sq_nonneg (δ:ℝ)) (Nat.cast_nonneg (α:=ℝ) n)]
  have hbb : vectorNorm b ≤ κ*sqrt (n:ℝ) := by
    apply vectorNorm_le_of_sq_sum (by positivity)
    rw [mul_pow,sq_sqrt (Nat.cast_nonneg n)]
    exact hb
  rw [he]
  exact (vectorNorm_add_le d b).trans ((add_le_add hd hbb).trans_eq (by ring))

theorem observation_root_mesh_inclusion {T ρ : ℝ} (hT : 0<T) (hρ : 0<ρ)
    (hB : IsBrownianReal B P) :
    ∃ m : ℕ, 0 < m ∧ ∃ δ : ℝ≥0, 0<δ ∧ (m:ℝ)*(δ:ℝ)=T ∧
      (∀ k : Fin m,(k:ℝ)*(δ:ℝ)∈Icc 0 T) ∧
      (∀ n,(Measure.pi (fun _ : Fin n=>P)).real (meshModulusBad B m δ (ρ/4) n) ≤
        (m:ℝ)*exp (-(n:ℝ))) ∧
      ∀ n,(∀ j A K ε c : ℝ,∀ J : Matrix (Fin n) (Fin n) ℝ,∀ σ : Spin n,
        {ω | operatorBound K J ∧ ∃ t : ℝ≥0,(t:ℝ)≤T ∧
          rootBad j A ε c (ρ/2) J (observationField B σ t ω)} ⊆
          meshModulusBad B m δ (ρ/4) n ∪ ⋃ k : Fin m,
            {ω | (J,observationField B σ ((k:ℝ≥0)*δ) ω)∈literalBadPair j A K ε c ρ}) := by
  obtain ⟨δ₀,hδ₀,ht⟩ := meshModulusBad_measure hB (show 0<ρ/4 by positivity)
  obtain ⟨m,hm,δ,hδ,hδle,he,hk,hcover⟩ := finite_time_mesh hT (lt_min hδ₀ (show 0<ρ/4 by positivity))
  refine ⟨m,hm,δ,hδ,he,hk,fun n=>ht m δ hδ (hδle.trans (min_le_left _ _)) n,?_⟩
  intro n j A K ε c J σ ω hω
  rcases hω with ⟨hJ,t,htt,hroot⟩
  by_cases hmod : ω∈meshModulusBad B m δ (ρ/4) n
  · exact Or.inl hmod
  apply Or.inr
  obtain ⟨k,u,hu,htrepr⟩ := hcover (t:ℝ) ⟨t.2,htt⟩
  let u' : UnitInterval := ⟨u,hu⟩
  have hte : t=(k:ℝ≥0)*δ+δ*⟨u'.1,u'.2.1⟩ := by
    apply NNReal.coe_injective
    change (t:ℝ)=(k:ℝ)*(δ:ℝ)+(δ:ℝ)*u
    exact htrepr
  have hb : ∑ i,(B ((k:ℝ≥0)*δ+δ*⟨u'.1,u'.2.1⟩) (ω i)-B ((k:ℝ≥0)*δ) (ω i))^2 ≤
      (ρ/4)^2*(n:ℝ) := le_of_not_gt (fun hh=>hmod ⟨k,u',hh⟩)
  have hinc := observationField_increment σ ((k:ℝ≥0)*δ) δ u' ω (show 0≤ρ/4 by positivity) hb
  rw [← hte] at hinc
  have hd : (δ:ℝ)+ρ/4≤ρ/2 := by linarith [hδle.trans (min_le_right δ₀ (ρ/4))]
  have hinc' := hinc.trans (mul_le_mul_of_nonneg_right hd (sqrt_nonneg (n:ℝ)))
  have hr := rootBad_field_transfer J (observationField B σ t ω)
    (observationField B σ ((k:ℝ≥0)*δ) ω) hinc' hroot
  have hr' : rootBad j A ε c ρ J (observationField B σ ((k:ℝ≥0)*δ) ω) := by
    convert hr using 1; ring
  exact mem_iUnion.mpr ⟨k,hJ,hr'⟩
end SKGap.ObservationBridge

end
end

end OAI
