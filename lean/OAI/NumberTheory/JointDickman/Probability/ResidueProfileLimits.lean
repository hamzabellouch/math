import OAI.NumberTheory.JointDickman.Probability.EmpiricalResidueProfile

namespace OAI

/-! # Bounded arithmetic arrays give compatible bounded residue profiles -/

namespace JointDickman
open Finset Filter
open scoped Topology

/-- A sharper coefficient bound retains the density of the residue class. -/
theorem empiricalResidueCoefficient_density_bound (H : ℕ → ℕ → ℂ) {C : ℝ}
    (hH : ∀ N n, ‖H N n‖ ≤ C) (N : ℕ) (q : ℕ+) (a : ZMod (q : ℕ)) :
    ‖empiricalResidueCoefficient H N q a‖ ≤
      (q : ℕ) * C * ((∑ n ∈ range N,
        if (n : ZMod (q : ℕ)) = a then (1 : ℝ) else 0) / (N : ℝ)) := by
  classical
  have hs := norm_sum_le_of_le (range N) (fun n _ => show
      ‖if (n : ZMod (q : ℕ)) = a then H N n else 0‖ ≤
        C * (if (n : ZMod (q : ℕ)) = a then 1 else 0) from by
    split_ifs <;> simp_all)
  rw [← mul_sum] at hs
  unfold empiricalResidueCoefficient
  rw [norm_mul, norm_div, Complex.norm_natCast, Complex.norm_natCast]
  calc
    _ ≤ (q : ℕ) * ((C * ∑ n ∈ range N,
      if (n : ZMod (q : ℕ)) = a then (1 : ℝ) else 0) / (N : ℝ)) := by
      gcongr
    _ = _ := by ring

theorem residueCoefficient_limit_bound (H : ℕ → ℕ → ℂ) {C : ℝ}
    (hH : ∀ N n, ‖H N n‖ ≤ C) {s : ℕ → ℕ} (hs : StrictMono s)
    {q : ℕ+} {a : ZMod (q : ℕ)} {z : ℂ}
    (hz : Tendsto (fun N => empiricalResidueCoefficient H (s N) q a) atTop (nhds z)) :
    ‖z‖ ≤ C := by
  classical
  have hcnt := real_periodic_moment_tendsto
    (fun b : ZMod (q : ℕ) => if b = a then (1 : ℝ) else 0) 1
  simp only [pow_one, sum_ite_eq', mem_univ, ite_true] at hcnt
  have hlim : Tendsto (fun N => ((q : ℕ) : ℝ)*C *
      ((∑ n ∈ range (s N), if (n : ZMod (q : ℕ)) = a then (1 : ℝ) else 0) / (s N : ℝ)))
      atTop (nhds (((q : ℕ) : ℝ)*C * (1 / ((q : ℕ) : ℝ)))) :=
    tendsto_const_nhds.mul (hcnt.comp hs.tendsto_atTop)
  have hle := le_of_tendsto_of_tendsto' hz.norm hlim
    (fun N => empiricalResidueCoefficient_density_bound H hH (s N) q a)
  have hq : ((q : ℕ) : ℝ) ≠ 0 := by exact_mod_cast q.ne_zero
  convert hle using 1; field_simp

theorem residueCoefficient_test_limit (H : ℕ → ℕ → ℂ) (s : ℕ → ℕ)
    (V : (q : ℕ+) → ZMod (q : ℕ) → ℂ)
    (hV : ∀ q a, Tendsto (fun N => empiricalResidueCoefficient H (s N) q a) atTop (nhds (V q a)))
    (q : ℕ+) (f : ZMod (q : ℕ) → ℂ) :
    Tendsto (fun N => empiricalResidueTest H (s N) f) atTop
      (nhds (residueMean (fun a => V q a * f a))) := by
  have h := (tendsto_finsetSum univ (fun a _ => (hV q a).mul_const (f a))).div_const
    (((q : ℕ) : ℂ))
  change Tendsto (fun N => residueMean (fun a => empiricalResidueCoefficient H (s N) q a * f a))
    atTop (nhds (residueMean (fun a => V q a * f a))) at h
  simpa only [empiricalResidueCoefficient_test] using h

theorem residueLift_natCast {d q : ℕ} [NeZero d] [NeZero q] (hd : d ∣ q)
    (f : ZMod d → ℂ) (n : ℕ) : residueLift (q := q) f (n : ZMod q) = f (n : ZMod d) := by
  unfold residueLift
  congr 1
  rw [ZMod.val_natCast, ZMod.natCast_eq_natCast_iff', Nat.mod_mod_of_dvd n hd]

theorem residueCoefficient_limit_compatible (H : ℕ → ℕ → ℂ) (s : ℕ → ℕ)
    (V : (q : ℕ+) → ZMod (q : ℕ) → ℂ)
    (hV : ∀ q a, Tendsto (fun N => empiricalResidueCoefficient H (s N) q a) atTop (nhds (V q a)))
    (d q : ℕ+) (hd : (d : ℕ) ∣ (q : ℕ)) (f : ZMod (d : ℕ) → ℂ) :
    residueMean (fun a => V q a * residueLift f a) = residueMean (fun a => V d a * f a) := by
  have hq := residueCoefficient_test_limit H s V hV q (residueLift f)
  have hd' := residueCoefficient_test_limit H s V hV d f
  have he (N : ℕ) : empiricalResidueTest H (s N) (residueLift (q := (q : ℕ)) f) =
      empiricalResidueTest H (s N) f := by
    unfold empiricalResidueTest
    simp only [residueLift_natCast hd]
  simp only [he] at hq
  exact tendsto_nhds_unique hq hd'

/-- Compactness produces the full profile, including its compatibility and
uniform energy bound; neither property is an additional analytic input. -/
theorem exists_residueProfile (H : ℕ → ℕ → ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hH : ∀ N n, ‖H N n‖ ≤ C) :
    ∃ (s : ℕ → ℕ), StrictMono s ∧ ∃ W : ResidueProfile,
      (∀ q a, ‖W.value q a‖ ≤ C) ∧
      ∀ (q : ℕ+) (f : ZMod (q : ℕ) → ℂ),
        Tendsto (fun N => empiricalResidueTest H (s N) f) atTop
          (nhds (residueMean (fun a => W.value q a * f a))) := by
  obtain ⟨s,hs,V,hV⟩ := empiricalResidueCoefficient_subsequence H hC hH
  have hbound (q : ℕ+) (a : ZMod (q : ℕ)) : ‖V q a‖ ≤ C :=
    residueCoefficient_limit_bound H hH hs (hV q a)
  have henergy (q : ℕ+) : residueEnergy (V q) ≤ C^2 := by
    unfold residueEnergy
    have hq : (0 : ℝ) < (q : ℕ) := by exact_mod_cast q.pos
    apply (div_le_iff₀ hq).mpr
    calc
      _ ≤ ∑ _a : ZMod (q : ℕ), C^2 := sum_le_sum fun a _ =>
        pow_le_pow_left₀ (norm_nonneg _) (hbound q a) 2
      _ = _ := by simp [mul_comm]
  let W : ResidueProfile := {
    value := V
    compatible := residueCoefficient_limit_compatible H s V hV
    energy_bounded := ⟨C^2, by rintro _ ⟨q,rfl⟩; exact henergy q⟩ }
  exact ⟨s,hs,W,hbound,residueCoefficient_test_limit H s V hV⟩

end JointDickman

end OAI
