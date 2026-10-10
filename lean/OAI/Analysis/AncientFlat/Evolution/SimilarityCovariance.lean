import OAI.Analysis.AncientFlat.Evolution.EvolutionFamily
import OAI.Analysis.AncientFlat.Evolution.DilationDerivatives
import OAI.Analysis.AncientFlat.Evolution.DilationCore

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff ZeroAtInfty BoundedContinuousFunction Laplacian
namespace ParametrixEvolution
open ParametrixDilation
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]
variable {α β T : ℝ} {A : C(ℝ,V →ᵇ Icc α β)} {b : C(ℝ,V →ᵇ ℂ)}
  {d : C₀(V,ℂ)} {u : ℝ → C₀(V,ℂ)}
lemma Evolves.end_mono (hu : Evolves A b 0 1 d u) (hT : T≤1) :
    Evolves A b 0 T d u := by
  refine ⟨hu.1,hu.2.1.mono (Icc_subset_Icc_right hT),?_,?_,?_⟩
  · intro t ht; exact hu.2.2.1 t ⟨ht.1,ht.2.trans_le hT⟩
  · intro t ht; exact hu.2.2.2.1 t ⟨ht.1,ht.2.trans_le hT⟩
  · intro t ht; exact hu.2.2.2.2 t ⟨ht.1,ht.2.trans_le hT⟩

omit [FiniteDimensional ℝ V] in
lemma moving_covariance (Af : V → ℝ) (Bf : V → ℂ)
    (hmoveA : ∀ t ∈ Icc (0:ℝ) 1, ∀ x,
      (A t x).val=Real.exp (-t)/16*Af (Real.exp (t/4) • x))
    (hmoveb : ∀ t ∈ Icc (0:ℝ) 1, ∀ x,
      b t x=1/2+Bf (Real.exp (t/4) • x))
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0≤t) (hst : s+t≤1) (x : V) :
    (A (s+t) (Real.exp (-s/4) • x)).val=
      Real.exp (-s)*(A t x).val ∧
    b (s+t) (Real.exp (-s/4) • x)=b t x := by
  have hst' : s+t ∈ Icc (0:ℝ) 1 := ⟨add_nonneg hs ht,hst⟩
  have ht' : t ∈ Icc (0:ℝ) 1 := ⟨ht,by linarith⟩
  have hsc : Real.exp ((s+t)/4) • Real.exp (-s/4) • x=Real.exp (t/4) • x := by
    rw [smul_smul,←Real.exp_add,show (s+t)/4+-s/4=t/4 by ring]
  constructor
  · rw [hmoveA _ hst',hmoveA _ ht',hsc,show -(s+t)=-s + -t by ring,Real.exp_add]
    ring
  · rw [hmoveb _ hst',hmoveb _ ht',hsc]

lemma exp_quarter_four (s : ℝ) : Real.exp (-s/4)^4=Real.exp (-s) := by
  rw [←Real.exp_nat_mul]
  congr 1
  ring

lemma Evolves.dilate_shift (hu : Evolves A b 0 1 d u)
    (Af : V → ℝ) (Bf : V → ℂ)
    (hmoveA : ∀ t ∈ Icc (0:ℝ) 1, ∀ x,
      (A t x).val=Real.exp (-t)/16*Af (Real.exp (t/4) • x))
    (hmoveb : ∀ t ∈ Icc (0:ℝ) 1, ∀ x,
      b t x=1/2+Bf (Real.exp (t/4) • x))
    {s : ℝ} (hs : s ∈ Icc (0:ℝ) 1) :
    Evolves A b 0 (1-s) (dil s (u s)) (fun t => dil s (u (s+t))) := by
  let : NormedAddCommGroup C₀(V,ℂ) := inferInstance
  let : NormedSpace ℂ C₀(V,ℂ) := inferInstance
  let : NormedAddCommGroup (V →ᵇ ℂ) := inferInstance
  let : NormedSpace ℝ (V →ᵇ ℂ) := inferInstance
  have hst (t : ℝ) (ht : t ∈ Ioo (0:ℝ) (1-s)) : s+t ∈ Ioo (0:ℝ) 1 :=
    ⟨by linarith [hs.1,ht.1],by linarith [ht.2]⟩
  refine ⟨by simp,?_,?_,?_,?_⟩
  · apply (dil s).continuous.comp_continuousOn
    apply hu.2.1.comp (continuous_const.add continuous_id).continuousOn
    intro t ht
    change s+t ∈ Icc (0:ℝ) 1
    exact ⟨by linarith [hs.1,ht.1],by linarith [ht.2]⟩
  · intro t ht
    exact (hu.2.2.1 _ (hst t ht)).comp (contDiff_const.smul contDiff_id)
  · intro t ht
    exact bounded_jets_scale _ _ (hu.2.2.1 _ (hst t ht)) (hu.2.2.2.1 _ (hst t ht))
  · intro t ht
    obtain ⟨p,hp,hpe⟩ := hu.2.2.2.2 _ (hst t ht)
    let Q : (V →ᵇ ℂ) →L[ℝ] (V →ᵇ ℂ) := BoundedContinuousFunction.compContinuousCLM ℂ ℝ (dilMap s)
    have ht' : HasDerivAt (fun r => (u (s+r)).toBCF) p t := by
      have ha : HasDerivAt (fun r : ℝ => s+r) 1 t := (hasDerivAt_id t).const_add s
      convert hp.scomp t ha using 1 <;> first | rfl | simp only [one_smul]
    refine ⟨Q p,?_,?_⟩
    · convert Q.hasFDerivAt.comp_hasDerivAt t ht' using 1
      rfl
    · intro x
      change p (Real.exp (-s/4) • x)=_
      rw [hpe]
      have hc := moving_covariance Af Bf hmoveA hmoveb hs.1 ht.1.le (by linarith [ht.2]) x
      rw [hc.1,hc.2]
      change _=-((A t x).val : ℂ)*Δ (Δ (fun y => u (s+t) (Real.exp (-s/4) • y))) x-
        b t x*u (s+t) (Real.exp (-s/4) • x)
      rw [bilaplacian_scale _ _ (hu.2.2.1 _ (hst t ht)),exp_quarter_four]
      simp only [Complex.ofReal_mul,Complex.real_smul]
      ring
end ParametrixEvolution

end

end OAI
