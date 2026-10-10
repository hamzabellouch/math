import OAI.Geometry.NodalSets.Elliptic.UniformSmoothBounds

namespace OAI

namespace Yau.Jets
open MvPolynomial
open scoped ContDiff
noncomputable section
variable {T : Type*} [TopologicalSpace T]

def UniformSmoothBounded (s : Set T) (R : ℝ) (f : T → Coord → ℂ) : Prop :=
  (∀ t, ContDiff ℝ ∞ (f t)) ∧
    ∀ k, ∃ C > 0, ∀ t ∈ s, ∀ x : Coord, ‖x‖ ≤ R → DerivativeBound k (f t) x C

lemma uniformSmoothBounded_of_continuous_derivatives (s : Set T) (hs : IsCompact s)
    (R : ℝ) (f : T → Coord → ℂ) (hf : ∀ t, ContDiff ℝ ∞ (f t))
    (hc : ∀ j, Continuous (fun z : T × Coord ↦ iteratedFDeriv ℝ j (f z.1) z.2)) :
    UniformSmoothBounded s R f :=
  ⟨hf, fun k ↦ compact_smooth_derivative_bound f k (fun j _ ↦ hc j) s hs R⟩

lemma ContinuousPolyFamily.derivative_continuous {P : T → CPoly}
    (hp : ContinuousPolyFamily P) (k : ℕ) :
    Continuous (fun z : T × Coord ↦ iteratedFDeriv ℝ k (reval (P z.1)) z.2) := by
  obtain ⟨r, hr⟩ := hp.2
  have he (t : T) : reval (P t) = polynomialFamily
      (fun d : r ↦ monomial d.val (1 : ℂ)) (fun t d ↦ (P t).coeff d.val) t := by
    funext x
    rw [polynomial_sum_of_support_subset (P t) r (hr t)]
    simp [polynomialFamily, reval, Algebra.smul_def]
    exact (Finset.sum_attach r (fun d ↦ (P t).coeff d *
      eval (fun i ↦ (x i : ℂ)) (monomial d (1 : ℂ)))).symm
  simp_rw [he]
  exact polynomialFamily_derivative_continuous
    (fun d : r ↦ monomial d.val (1 : ℂ)) (fun t d ↦ (P t).coeff d.val)
    (fun d ↦ hp.1 d.val) k

lemma ContinuousPolyFamily.uniformSmoothBounded {P : T → CPoly}
    (hp : ContinuousPolyFamily P) (s : Set T) (hs : IsCompact s) (R : ℝ) :
    UniformSmoothBounded s R (fun t ↦ reval (P t)) := by
  apply uniformSmoothBounded_of_continuous_derivatives s hs R _ (fun t ↦ reval_contDiff _)
  exact hp.derivative_continuous

omit [TopologicalSpace T]

lemma UniformSmoothBounded.const (s : Set T) (R : ℝ) (c : ℂ) :
    UniformSmoothBounded s R (fun _ _ ↦ c) := by
  refine ⟨fun _ ↦ contDiff_const, fun k ↦ ⟨‖c‖ + 1, by positivity, ?_⟩⟩
  intro t ht x hx j hj
  cases j with
  | zero => simp [norm_iteratedFDeriv_zero]
  | succ j => simp [iteratedFDeriv_succ_const]; positivity

lemma UniformSmoothBounded.add {s : Set T} {R : ℝ} {f g : T → Coord → ℂ}
    (hf : UniformSmoothBounded s R f) (hg : UniformSmoothBounded s R g) :
    UniformSmoothBounded s R (fun t x ↦ f t x + g t x) := by
  refine ⟨fun t ↦ (hf.1 t).add (hg.1 t), ?_⟩
  intro k
  obtain ⟨A, hA, ha⟩ := hf.2 k
  obtain ⟨B, hB, hb⟩ := hg.2 k
  exact ⟨A+B, add_pos hA hB, fun t ht x hx ↦
    (ha t ht x hx).add (hf.1 t) (hg.1 t) (hb t ht x hx)⟩

lemma UniformSmoothBounded.mul {s : Set T} {R : ℝ} {f g : T → Coord → ℂ}
    (hf : UniformSmoothBounded s R f) (hg : UniformSmoothBounded s R g) :
    UniformSmoothBounded s R (fun t x ↦ f t x * g t x) := by
  refine ⟨fun t ↦ (hf.1 t).mul (hg.1 t), ?_⟩
  intro k
  obtain ⟨A, hA, ha⟩ := hf.2 k
  obtain ⟨B, hB, hb⟩ := hg.2 k
  exact ⟨2^k*A*B, by positivity, fun t ht x hx ↦
    (ha t ht x hx).mul (hf.1 t) (hg.1 t) hA.le hB.le (hb t ht x hx)⟩

lemma UniformSmoothBounded.sum {ι : Type*} (r : Finset ι) {s : Set T} {R : ℝ}
    {f : ι → T → Coord → ℂ} (hf : ∀ i ∈ r, UniformSmoothBounded s R (f i)) :
    UniformSmoothBounded s R (fun t x ↦ ∑ i ∈ r, f i t x) := by
  classical
  induction r using Finset.induction_on with
  | empty => simpa using UniformSmoothBounded.const s R 0
  | @insert i r hi ih =>
    simpa [Finset.sum_insert hi] using (hf i (Finset.mem_insert_self i r)).add
      (ih (fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)))

lemma UniformSmoothBounded.coordPartial {s : Set T} {R : ℝ} {f : T → Coord → ℂ}
    (hf : UniformSmoothBounded s R f) (i : Fin 4) :
    UniformSmoothBounded s R (fun t ↦ coordPartial i (f t)) := by
  refine ⟨fun t ↦ coordPartial_contDiff (hf.1 t) i, ?_⟩
  intro k
  obtain ⟨C, hC, hc⟩ := hf.2 (k+1)
  exact ⟨C, hC, fun t ht x hx ↦ (hc t ht x hx).coordPartial (hf.1 t) i⟩

lemma uniformSmoothBounded_secondOrder {s : Set T} {R : ℝ}
    {g : T → Fin 4 → Fin 4 → Coord → ℂ} {b : T → Fin 4 → Coord → ℂ}
    {f : T → Coord → ℂ}
    (hg : ∀ i j, UniformSmoothBounded s R (fun t ↦ g t i j))
    (hb : ∀ i, UniformSmoothBounded s R (fun t ↦ b t i))
    (hf : UniformSmoothBounded s R f) :
    UniformSmoothBounded s R (fun t ↦ smoothSecondOrder (g t) (b t) (f t)) := by
  exact (UniformSmoothBounded.sum Finset.univ (fun i _ ↦
    UniformSmoothBounded.sum Finset.univ (fun j _ ↦
      (hg i j).mul ((hf.coordPartial j).coordPartial i)))).add
    (UniformSmoothBounded.sum Finset.univ (fun i _ ↦ (hb i).mul (hf.coordPartial i)))

lemma uniformSmoothBounded_eikonal {s : Set T} {R : ℝ}
    {g : T → Fin 4 → Fin 4 → Coord → ℂ} {phi : T → Coord → ℂ}
    (hg : ∀ i j, UniformSmoothBounded s R (fun t ↦ g t i j))
    (hp : UniformSmoothBounded s R phi) :
    UniformSmoothBounded s R (fun t ↦ smoothEikonal (g t) (phi t)) := by
  exact (UniformSmoothBounded.sum Finset.univ (fun i _ ↦
    UniformSmoothBounded.sum Finset.univ (fun j _ ↦
      ((hg i j).mul (hp.coordPartial i)).mul (hp.coordPartial j)))).add
    (UniformSmoothBounded.const s R 4)

lemma uniformSmoothBounded_beamVector {s : Set T} {R : ℝ}
    {g : T → Fin 4 → Fin 4 → Coord → ℂ} {phi : T → Coord → ℂ}
    (hg : ∀ i j, UniformSmoothBounded s R (fun t ↦ g t i j))
    (hp : UniformSmoothBounded s R phi) (i : Fin 4) :
    UniformSmoothBounded s R (fun t ↦ smoothBeamVector (g t) (phi t) i) :=
  (UniformSmoothBounded.const s R 2).mul (UniformSmoothBounded.sum Finset.univ
    (fun j _ ↦ (hg i j).mul (hp.coordPartial j)))

lemma uniformSmoothBounded_beamScalar {s : Set T} {R : ℝ}
    {g : T → Fin 4 → Fin 4 → Coord → ℂ} {b : T → Fin 4 → Coord → ℂ}
    {phi : T → Coord → ℂ}
    (hg : ∀ i j, UniformSmoothBounded s R (fun t ↦ g t i j))
    (hb : ∀ i, UniformSmoothBounded s R (fun t ↦ b t i))
    (hp : UniformSmoothBounded s R phi) :
    UniformSmoothBounded s R (fun t ↦ smoothBeamScalar (g t) (b t) (phi t)) :=
  (uniformSmoothBounded_secondOrder hg hb hp).add (UniformSmoothBounded.const s R 6)

lemma uniformSmoothBounded_transport_defect {s : Set T} {R : ℝ}
    {g : T → Fin 4 → Fin 4 → Coord → ℂ} {b : T → Fin 4 → Coord → ℂ}
    {phi a prev : T → Coord → ℂ}
    (hg : ∀ i j, UniformSmoothBounded s R (fun t ↦ g t i j))
    (hb : ∀ i, UniformSmoothBounded s R (fun t ↦ b t i))
    (hp : UniformSmoothBounded s R phi) (ha : UniformSmoothBounded s R a)
    (hprev : UniformSmoothBounded s R prev) :
    UniformSmoothBounded s R (fun t x ↦
      smoothTransport (smoothBeamVector (g t) (phi t)) (smoothBeamScalar (g t) (b t) (phi t))
        (fun _ ↦ 0) (a t) x + smoothSecondOrder (g t) (b t) (prev t) x) := by
  have h := ((UniformSmoothBounded.sum Finset.univ (fun i _ ↦
    (uniformSmoothBounded_beamVector hg hp i).mul (ha.coordPartial i))).add
    ((uniformSmoothBounded_beamScalar hg hb hp).mul ha)).add
      (uniformSmoothBounded_secondOrder hg hb hprev)
  simpa [smoothTransport] using h

end
end Yau.Jets

end OAI
