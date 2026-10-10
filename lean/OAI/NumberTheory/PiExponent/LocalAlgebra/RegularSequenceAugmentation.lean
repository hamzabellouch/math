import OAI.NumberTheory.PiExponent.LocalAlgebra.ConeComplex

namespace OAI

namespace PiExponentSiegelAux.W30

variable {R X Y : Type*} [CommRing R]
variable [AddCommGroup X] [AddCommGroup Y] [Module R X] [Module R Y]

theorem coneBottom_range_eq_sup (g : Y →ₗ[R] R) (r : R) (I : Ideal R)
    (hg : LinearMap.range g = I) :
    LinearMap.range (coneBottom g r) = I ⊔ Ideal.span {r} := by
  have heq : coneBottom g r = g.coprod (r • LinearMap.id) := rfl
  rw [heq, LinearMap.range_coprod, hg]
  congr 1
  ext z
  simp only [LinearMap.mem_range, LinearMap.smul_apply, LinearMap.id_apply,
    smul_eq_mul, Ideal.mem_span_singleton, dvd_def]
  exact exists_congr (fun _ => eq_comm)

theorem coneBottom_range_eq_append_quotient_kernel (g : Y →ₗ[R] R)
    (xs : List R) (r : R) (hg : LinearMap.range g = Ideal.ofList xs) :
    LinearMap.range (coneBottom g r) = LinearMap.ker (Ideal.ofList (xs ++ [r])).mkQ := by
  rw [Submodule.ker_mkQ, coneBottom_range_eq_sup g r _ hg,
    Ideal.ofList_append, Ideal.ofList_singleton]

theorem regular_sequence_prefix_quotient (xs : List R)
    (hreg : RingTheory.Sequence.IsRegular R xs) (i : ℕ) (hi : i < xs.length) :
    IsSMulRegular (R ⧸ Ideal.ofList (xs.take i)) xs[i] := by
  have hI : (Ideal.ofList (xs.take i) • (⊤ : Submodule R R)) =
      Ideal.ofList (xs.take i) := by
    change Ideal.ofList (xs.take i) * ⊤ = Ideal.ofList (xs.take i)
    exact Ideal.mul_top _
  have h := hreg.toIsWeaklyRegular.regular_mod_prev i hi
  rw [hI] at h
  exact h

theorem regular_sequence_cone_bottom_exact (xs : List R)
    (hreg : RingTheory.Sequence.IsRegular R xs) (i : ℕ) (hi : i < xs.length)
    (f : X →ₗ[R] Y) (g : Y →ₗ[R] R)
    (hfg : LinearMap.range f = LinearMap.ker g)
    (hg : LinearMap.range g = Ideal.ofList (xs.take i)) :
    LinearMap.range (coneDifferential f g xs[i]) =
      LinearMap.ker (coneBottom g xs[i]) := by
  apply coneBottom_exact f g (Ideal.ofList (xs.take i)).mkQ xs[i] hfg
  · simpa only [Submodule.ker_mkQ] using hg
  · exact regular_sequence_prefix_quotient xs hreg i hi

theorem appended_augmentation_surjective (xs : List R) (r : R) :
    Function.Surjective (Ideal.ofList (xs ++ [r])).mkQ :=
  Submodule.mkQ_surjective _

end PiExponentSiegelAux.W30

end OAI
