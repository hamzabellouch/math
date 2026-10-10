import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.Periodization

namespace OAI

noncomputable section
namespace VelocityDetection.Periodization
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators
open SpatialCalculus JointCalculus PeriodicSpace
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem support_dAlong {K : Set (Coord n)} (hK : IsClosed K)
    {f : ℝ → Coord n → E} (hs : ∀ t X, f t X ≠ 0 → X ∈ K)
    (v : ℝ × Coord n) (t : ℝ) (X : Coord n)
    (h : dAlong v (uncurry f) (t,X) ≠ 0) : X ∈ K := by
  by_contra hX
  have hv : ∀ᶠ q : ℝ × Coord n in 𝓝 (t,X), q.2 ∉ K :=
    (hK.isOpen_compl.preimage continuous_snd).mem_nhds hX
  have he : uncurry f =ᶠ[𝓝 (t,X)] 0 := hv.mono (fun q hq => by
    exact not_not.mp (fun hn => hq (hs q.1 q.2 hn)))
  have hz := (eventuallyEq_dAlong v he).eq_of_nhds
  exact h (by simpa [dAlong] using hz)

theorem boundedSupport_dAlong {f : ℝ → Coord n → E} {C : ℝ}
    (hs : ∀ t X, f t X ≠ 0 → ∀ i, |X i| ≤ C)
    (v : ℝ × Coord n) :
    ∀ t X, dAlong v (uncurry f) (t,X) ≠ 0 → ∀ i, |X i| ≤ C := by
  have hK : IsClosed {X : Coord n | ∀ i, |X i| ≤ C} := by
    rw [Set.ofPred_forall]
    exact isClosed_iInter (fun i => isClosed_le (continuous_apply i).abs continuous_const)
  exact support_dAlong hK hs v

theorem dAlong_extend {f : ℝ → Coord n → E} {C : ℝ}
    (hf : ContDiff ℝ ∞ (uncurry f))
    (hs : ∀ t X, f t X ≠ 0 → ∀ i, |X i| ≤ C)
    (v : ℝ × Coord n) (t : ℝ) (X : Coord n) :
    dAlong v (uncurry (extend f)) (t,X) =
      extend (fun s Y => dAlong v (uncurry f) (s,Y)) t X := by
  classical
  obtain ⟨N,hN⟩ := exists_nat_gt (‖X‖+C)
  have he : uncurry (extend f) =ᶠ[𝓝 (t,X)]
      (fun q => ∑ k ∈ box (n := n) N, f q.1 (q.2-lattice k)) := by
    have hv : ∀ᶠ q : ℝ × Coord n in 𝓝 (t,X), ‖q.2‖+C < N :=
      (isOpen_lt (continuous_snd.norm.add_const C) continuous_const).mem_nhds hN
    exact hv.mono (fun q hq => extend_finite hs hq q.1)
  rw [(eventuallyEq_dAlong v he).eq_of_nhds,extend_finite (boundedSupport_dAlong hs v) hN t]
  unfold dAlong
  let g : (Fin n → ℤ) → (ℝ × Coord n) → E := fun k q => f q.1 (q.2-lattice k)
  have hg (k : Fin n → ℤ) : ContDiff ℝ ∞ (g k) :=
    hf.comp (contDiff_fst.prodMk (contDiff_snd.sub contDiff_const))
  have hsum : (fun q : ℝ × Coord n => ∑ k ∈ box (n := n) N, f q.1 (q.2-lattice k)) =
      ∑ k ∈ box (n := n) N, g k := by ext q; simp only [Finset.sum_apply,g]
  rw [hsum,fderiv_sum (fun k _ => (hg k).differentiable (by simp) (t,X)),sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  have hek : g k = fun q => uncurry f (q + (0,-lattice k)) := by
    funext q
    dsimp [g,uncurry]
    rw [add_zero,sub_eq_add_neg]
  rw [hek,fderiv_comp_add_right]
  simp only [Prod.mk_add_mk,add_zero,sub_eq_add_neg]

theorem deriv_eq_dAlong {f : ℝ → Coord n → E}
    (hf : ContDiff ℝ ∞ (uncurry f)) (t : ℝ) (X : Coord n) :
    deriv (fun s => f s X) t = dAlong (1,0) (uncurry f) (t,X) := by
  have hh := (hf.differentiable (by simp) (t,X)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t X))
  simpa only [comp_def,id_eq,uncurry_apply_pair,dAlong] using hh.deriv

theorem deriv_extend {f : ℝ → Coord n → E} {C : ℝ}
    (hf : ContDiff ℝ ∞ (uncurry f))
    (hs : ∀ t X, f t X ≠ 0 → ∀ i, |X i| ≤ C) (t : ℝ) (X : Coord n) :
    deriv (fun s => extend f s X) t = extend (fun s Y => deriv (fun r => f r Y) s) t X := by
  simp_rw [deriv_eq_dAlong (contDiff_extend hf hs),deriv_eq_dAlong hf]
  exact dAlong_extend hf hs (1,0) t X

theorem spatialD_extend {f : ScalarField n} {C : ℝ}
    (hf : ContDiff ℝ ∞ (uncurry f))
    (hs : ∀ t X, f t X ≠ 0 → ∀ i, |X i| ≤ C) (i : Fin n) :
    spatialD i (extend f) = extend (spatialD i f) := by
  funext t X
  rw [spatialD_eq (contDiff_extend hf hs)]
  have he : spatialD i f = fun s Y => dAlong (0,Pi.single i 1) (uncurry f) (s,Y) :=
    funext (fun s => funext (spatialD_eq hf i s))
  rw [he]
  exact dAlong_extend hf hs (0,Pi.single i 1) t X

theorem boundedSupport_spatialD {f : ScalarField n} {C : ℝ}
    (hf : ContDiff ℝ ∞ (uncurry f))
    (hs : ∀ t X, f t X ≠ 0 → ∀ i, |X i| ≤ C) (i : Fin n) :
    ∀ t X, spatialD i f t X ≠ 0 → ∀ j, |X j| ≤ C := by
  simp_rw [spatialD_eq hf]
  exact boundedSupport_dAlong hs (0,Pi.single i 1)

theorem extend_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → Coord n → E) {C : ℝ}
    (hs : ∀ k ∈ s, ∀ t X, f k t X ≠ 0 → ∀ i, |X i| ≤ C) :
    extend (fun t X => ∑ k ∈ s, f k t X) = fun t X => ∑ k ∈ s, extend (f k) t X := by
  classical
  funext t X
  obtain ⟨N,hN⟩ := exists_nat_gt (‖X‖+C)
  have hsum : ∀ t X, (∑ k ∈ s, f k t X) ≠ 0 → ∀ i, |X i| ≤ C := by
    intro r Y hY
    obtain ⟨k,hk,h⟩ := Finset.exists_ne_zero_of_sum_ne_zero hY
    exact hs k hk r Y h
  rw [extend_finite hsum hN]
  simp_rw [Finset.sum_comm (s := box (n := n) N) (t := s)]
  exact Finset.sum_congr rfl (fun k hk => (extend_finite (hs k hk) hN t).symm)

theorem laplacian_extend {f : ScalarField n} {C : ℝ}
    (hf : ContDiff ℝ ∞ (uncurry f))
    (hs : ∀ t X, f t X ≠ 0 → ∀ i, |X i| ≤ C) :
    laplacian (extend f) = extend (laplacian f) := by
  have hfd (i : Fin n) := TailSpace.Jets.contDiff_uncurry_spatialD hf i
  have hsd (i : Fin n) := boundedSupport_spatialD hf hs i
  have hdd (i : Fin n) : spatialD i (spatialD i (extend f)) =
      extend (spatialD i (spatialD i f)) := by
    rw [spatialD_extend hf hs,spatialD_extend (hfd i) (hsd i)]
  funext t X
  unfold laplacian
  simp_rw [hdd]
  exact congrFun (congrFun (extend_sum Finset.univ (fun i => spatialD i (spatialD i f))
    (fun i _ => boundedSupport_spatialD (hfd i) (hsd i) i)) t) X |>.symm

theorem abs_extend_le {f : ScalarField n} {B : ℝ}
    (hs : ∀ t X, f t X ≠ 0 → ∀ i, X i ∈ Ioo (0:ℝ) 1)
    (hb : ∀ t X, |f t X| ≤ B) (t : ℝ) (X : Coord n) : |extend f t X| ≤ B := by
  let k : Fin n → ℤ := fun i => ⌊X i⌋
  let Y : Coord n := X-lattice k
  have hY : ∀ i, Y i ∈ Icc (0:ℝ) 1 := fun i =>
    ⟨Int.fract_nonneg (X i),(Int.fract_lt_one (X i)).le⟩
  have he : X = Y+lattice k := by dsimp [Y]; abel
  rw [he,extend_add_lattice,extend_eq_chart hs t hY]
  exact hb t Y

theorem extend_periodic_mul (a : ScalarField n) (f : ScalarField n)
    (hp : ∀ t, FactorsThrough (a t) cover) :
    extend (fun t X => a t X*f t X) = fun t X => a t X*extend f t X := by
  funext t X
  have h (k : Fin n → ℤ) : a t (X-lattice k) = a t X := by
    apply hp t
    apply cover_eq_iff.mpr
    refine ⟨-k,?_⟩
    ext i
    simp [lattice,sub_eq_add_neg]
  simp only [extend,h,tsum_mul_left]

end VelocityDetection.Periodization
end

end OAI
