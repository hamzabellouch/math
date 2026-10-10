import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.PeriodicSpaceRestrictRestrict

namespace OAI

noncomputable section
namespace VelocityDetection.Periodization
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators
open PeriodicSpace
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def lattice (k : Fin n → ℤ) : Coord n := fun i => (k i : ℝ)

@[simp] theorem lattice_zero : lattice (0 : Fin n → ℤ) = 0 := by ext; simp [lattice]

@[simp] theorem lattice_add (k l : Fin n → ℤ) : lattice (k+l) = lattice k + lattice l := by
  ext; simp [lattice]

def extend (f : ℝ → Coord n → E) (t : ℝ) (X : Coord n) : E :=
  ∑' k : Fin n → ℤ, f t (X-lattice k)

def box (N : ℕ) : Finset (Fin n → ℤ) :=
  Finset.Icc (fun _ => -(N:ℤ)) (fun _ => (N:ℤ))

theorem extend_finite {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → Coord n → E} {C : ℝ}
    (hf : ∀ t X, f t X ≠ 0 → ∀ i, |X i| ≤ C) {N : ℕ} {X : Coord n}
    (hX : ‖X‖ + C < N) (t : ℝ) :
    extend f t X = ∑ k ∈ box (n := n) N, f t (X-lattice k) := by
  classical
  apply tsum_eq_sum
  intro k hk
  by_contra hn
  have hle : ∀ i, -(N:ℤ) ≤ k i ∧ k i ≤ (N:ℤ) := by
    intro i
    have hh := hf t (X-lattice k) hn i
    have hi : |X i| ≤ ‖X‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm X i
    change |X i - (k i:ℝ)| ≤ C at hh
    have hb : -(N:ℝ) < (k i:ℝ) ∧ (k i:ℝ) < N := by
      obtain ⟨ha,hb⟩ := abs_le.mp hh
      obtain ⟨hc,hd⟩ := abs_le.mp hi
      constructor <;> linarith
    exact ⟨by exact_mod_cast hb.1.le, by exact_mod_cast hb.2.le⟩
  exact hk (Finset.mem_Icc.mpr ⟨fun i => (hle i).1, fun i => (hle i).2⟩)

theorem contDiff_extend {f : ℝ → Coord n → E} {C : ℝ} {r : ℕ∞}
    (hf : ContDiff ℝ r (uncurry f))
    (hs : ∀ t X, f t X ≠ 0 → ∀ i, |X i| ≤ C) :
    ContDiff ℝ r (uncurry (extend f)) := by
  classical
  apply contDiff_iff_contDiffAt.mpr
  intro p
  obtain ⟨N,hN⟩ := exists_nat_gt (‖p.2‖ + C)
  have hh : ContDiff ℝ r (fun q : ℝ × Coord n =>
      ∑ k ∈ box (n := n) N, f q.1 (q.2-lattice k)) := by
    apply ContDiff.sum
    intro k _
    exact hf.comp (contDiff_fst.prodMk (contDiff_snd.sub contDiff_const))
  apply hh.contDiffAt.congr_of_eventuallyEq
  have hv : ∀ᶠ q : ℝ × Coord n in 𝓝 p, ‖q.2‖+C < N :=
    (isOpen_lt (continuous_snd.norm.add_const C) continuous_const).mem_nhds hN
  exact hv.mono (fun q hq => extend_finite hs hq q.1)

theorem extend_add_lattice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → Coord n → E) (t : ℝ) (X : Coord n)
    (k : Fin n → ℤ) : extend f t (X+lattice k) = extend f t X := by
  unfold extend
  have hh := (Equiv.addRight k).tsum_eq (fun l => f t (X+lattice k-lattice l))
  convert hh.symm using 1
  apply tsum_congr
  intro l
  congr 1
  change X - lattice l = X + lattice k - lattice (l+k)
  rw [lattice_add]
  abel

theorem cover_eq_iff {X Y : Coord n} :
    cover X = cover Y ↔ ∃ k : Fin n → ℤ, X = Y+lattice k := by
  constructor
  · intro h
    have hh (i : Fin n) : ∃ k : ℤ, (k:ℝ) = X i-Y i := by
      have hi : ((X i-Y i : ℝ) : AddCircle (1:ℝ)) = 0 := by
        change cover (X-Y) i = 0
        rw [cover_sub,h,sub_self]
        rfl
      simpa using ((AddCircle.coe_eq_zero_iff (1:ℝ)).mp hi)
    choose k hk using hh
    refine ⟨k,?_⟩
    ext i
    change X i = Y i+(k i:ℝ)
    rw [hk]
    ring
  · rintro ⟨k,rfl⟩
    rw [cover_add]
    have hz : cover (lattice k) = 0 := by
      ext i
      apply (AddCircle.coe_eq_zero_iff (1:ℝ)).mpr
      exact ⟨k i,by simp [lattice]⟩
    rw [hz,add_zero]

theorem periodic_extend (f : ℝ → Coord n → E) (t : ℝ) :
    FactorsThrough (extend f t) cover := by
  intro X Y h
  obtain ⟨k,rfl⟩ := cover_eq_iff.mp h
  exact extend_add_lattice f t Y k

theorem extend_eq_chart {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → Coord n → E}
    (hs : ∀ t X, f t X ≠ 0 → ∀ i, X i ∈ Ioo (0:ℝ) 1)
    (t : ℝ) {X : Coord n} (hX : ∀ i, X i ∈ Icc (0:ℝ) 1) :
    extend f t X = f t X := by
  classical
  rw [extend, tsum_eq_single (0 : Fin n → ℤ)]
  · simp
  · intro k hk
    by_contra hn
    have hh := hs t (X-lattice k) hn
    have hz : k = 0 := by
      ext i
      have hi := hh i
      have hXi := hX i
      change 0 < X i - (k i:ℝ) ∧ X i - (k i:ℝ) < 1 at hi
      have hklo : (-1:ℝ) < (k i:ℝ) := by linarith [hXi.1,hi.2]
      have hkhi : (k i:ℝ) < 1 := by linarith [hXi.2,hi.1]
      have h₁ : (-1:ℤ) < k i := by exact_mod_cast hklo
      have h₂ : k i < (1:ℤ) := by exact_mod_cast hkhi
      change k i = 0
      omega
    exact hk hz

theorem extend_eventuallyEq_chart {f : ℝ → Coord n → E}
    (hs : ∀ t X, f t X ≠ 0 → ∀ i, X i ∈ Ioo (0:ℝ) 1)
    {p : ℝ × Coord n} (hp : ∀ i, p.2 i ∈ Ioo (0:ℝ) 1) :
    uncurry (extend f) =ᶠ[𝓝 p] uncurry f := by
  have ho : IsOpen {q : ℝ × Coord n | ∀ i, q.2 i ∈ Ioo (0:ℝ) 1} := by
    rw [Set.ofPred_forall]
    apply isOpen_iInter_of_finite
    intro i
    exact (isOpen_Ioo : IsOpen (Ioo (0:ℝ) 1)).preimage
      ((continuous_apply i).comp (continuous_snd : Continuous (Prod.snd : ℝ × Coord n → Coord n)))
  have hv : ∀ᶠ q : ℝ × Coord n in 𝓝 p, ∀ i, q.2 i ∈ Ioo (0:ℝ) 1 := ho.mem_nhds hp
  exact hv.mono (fun q hq => extend_eq_chart hs q.1 (fun i => ⟨(hq i).1.le,(hq i).2.le⟩))

end VelocityDetection.Periodization
end

end OAI
