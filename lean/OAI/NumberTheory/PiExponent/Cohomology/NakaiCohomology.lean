import OAI.NumberTheory.PiExponent.Cohomology.CohomologyIso

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

def cohomologyMap (p : X ⟶ Spec (CommRingCat.of ℂ)) {M N : X.Modules}
    (f : M ⟶ N) (n : ℕ) :
    let _ := Module.compHom (cohomology M n) (baseScalars p)
    let _ := Module.compHom (cohomology N n) (baseScalars p)
    cohomology M n →ₗ[ℂ] cohomology N n := by
  dsimp only
  letI := Module.compHom (cohomology M n) (baseScalars p)
  letI := Module.compHom (cohomology N n) (baseScalars p)
  let g := (Ext.mk₀ f).postcompOfLinear Γ(X,⊤) (structureSheaf X) (add_zero n)
  exact { g.toAddHom with map_smul' := fun r x => g.map_smul (baseScalars p r) x }

theorem globalSections_surjective_of_h1_stationary
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (hfinite₁ : let _ := Module.compHom (cohomology S.X₁ 1) (baseScalars p)
      FiniteDimensional ℂ (cohomology S.X₁ 1))
    (hfinite₂ : let _ := Module.compHom (cohomology S.X₂ 1) (baseScalars p)
      FiniteDimensional ℂ (cohomology S.X₂ 1))
    (hrank : cohomologyDimension p S.X₁ 1 = cohomologyDimension p S.X₂ 1)
    (hzero : ∀ z : cohomology S.X₃ 1, z = 0) :
    Function.Surjective (fun s : GlobalSections X S.X₂ => s ≫ S.g) := by
  let := Module.compHom (cohomology S.X₁ 1) (baseScalars p)
  let := Module.compHom (cohomology S.X₂ 1) (baseScalars p)
  have : FiniteDimensional ℂ (cohomology S.X₁ 1) := hfinite₁
  have : FiniteDimensional ℂ (cohomology S.X₂ 1) := hfinite₂
  let f := cohomologyMap p S.f 1
  have hsurj : Function.Surjective f := by
    intro b
    obtain ⟨a,ha⟩ := Ext.covariant_sequence_exact₂ (structureSheaf X) hS b (hzero _)
    exact ⟨a,ha⟩
  have hinj : Function.Injective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).mpr hsurj
  intro s
  have hboundary : (Ext.mk₀ s).comp hS.extClass rfl = 0 := by
    apply hinj
    change ((Ext.mk₀ s).comp hS.extClass rfl).comp (Ext.mk₀ S.f) (add_zero 1) = f 0
    rw [map_zero]
    rw [Ext.comp_assoc_of_third_deg_zero, hS.extClass_comp, Ext.comp_zero]
  obtain ⟨a,ha⟩ := Ext.covariant_sequence_exact₃ (structureSheaf X) hS (Ext.mk₀ s) rfl hboundary
  refine ⟨Ext.homEquiv₀ a, ?_⟩
  apply (Ext.mk₀_bijective (structureSheaf X) S.X₃).injective
  rw [← Ext.mk₀_comp_mk₀, Ext.mk₀_homEquiv₀_apply]
  exact ha

theorem eventually_constant_of_antitone_nat (a : ℕ → ℕ) (ha : Antitone a) :
    ∃ N, ∀ n, N ≤ n → a n = a N := by
  classical
  have he : ∃ k : ℕ, ∃ n, a n = k := ⟨a 0,0,rfl⟩
  obtain ⟨N,hN⟩ := Nat.find_spec he
  refine ⟨N,fun n hn => le_antisymm (ha hn) ?_⟩
  rw [hN]
  exact Nat.find_min' he ⟨n,rfl⟩

theorem eventual_globalSections_surjective
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (F Q : ℕ → X.Modules)
    (f : ∀ n, F n ⟶ F (n+1)) (g : ∀ n, F (n+1) ⟶ Q n)
    (hcomp : ∀ n, f n ≫ g n = 0)
    (hshort : ∀ n, (ShortComplex.mk (f n) (g n) (hcomp n)).ShortExact)
    (hfinite : ∀ n, let _ := Module.compHom (cohomology (F n) 1) (baseScalars p)
      FiniteDimensional ℂ (cohomology (F n) 1))
    (hzero : ∃ N, ∀ n, N ≤ n → ∀ z : cohomology (Q n) 1, z = 0) :
    ∃ N, ∀ n, N ≤ n →
      Function.Surjective (fun s : GlobalSections X (F (n+1)) => s ≫ g n) := by
  obtain ⟨N₀,hN₀⟩ := hzero
  have hdim (n : ℕ) (hn : N₀ ≤ n) :
      cohomologyDimension p (F (n+1)) 1 ≤ cohomologyDimension p (F n) 1 := by
    let := Module.compHom (cohomology (F n) 1) (baseScalars p)
    let := Module.compHom (cohomology (F (n+1)) 1) (baseScalars p)
    have : FiniteDimensional ℂ (cohomology (F n) 1) := hfinite n
    have hsurj : Function.Surjective (cohomologyMap p (f n) 1) := by
      intro b
      exact Ext.covariant_sequence_exact₂ (structureSheaf X) (hshort n) b (hN₀ n hn _)
    exact LinearMap.finrank_le_finrank_of_surjective hsurj
  let a : ℕ → ℕ := fun n => cohomologyDimension p (F (N₀+n)) 1
  have ha : Antitone a := antitone_nat_of_succ_le (fun n => by
    simpa only [a, Nat.add_assoc] using hdim (N₀+n) (Nat.le_add_right _ _))
  obtain ⟨N,hN⟩ := eventually_constant_of_antitone_nat a ha
  refine ⟨N₀+N,fun n hn => ?_⟩
  have hn₀ : N₀ ≤ n := by omega
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn₀
  have hk : N ≤ k := by omega
  have he : cohomologyDimension p (F (N₀+k)) 1 =
      cohomologyDimension p (F (N₀+k+1)) 1 := by
    exact (hN k hk).trans (by simpa only [a, Nat.add_assoc] using (hN (k+1) (by omega)).symm)
  exact globalSections_surjective_of_h1_stationary p
    (ShortComplex.mk (f (N₀+k)) (g (N₀+k)) (hcomp (N₀+k)))
    (hshort (N₀+k)) (hfinite _) (hfinite _) he (hN₀ _ (by omega))

theorem cohomologyMap_bijective_of_quotient_vanishing
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (n : ℕ) (hprev : ∀ z : cohomology S.X₃ n, z = 0)
    (hnext : ∀ z : cohomology S.X₃ (n+1), z = 0) :
    Function.Bijective (cohomologyMap p S.f (n+1)) := by
  let := Module.compHom (cohomology S.X₁ (n+1)) (baseScalars p)
  let := Module.compHom (cohomology S.X₂ (n+1)) (baseScalars p)
  constructor
  · apply (injective_iff_map_eq_zero (cohomologyMap p S.f (n+1))).mpr
    intro a ha
    obtain ⟨b,hb⟩ := Ext.covariant_sequence_exact₁ (structureSheaf X) hS a ha rfl
    rw [hprev b, Ext.zero_comp] at hb
    exact hb.symm
  · intro b
    exact Ext.covariant_sequence_exact₂ (structureSheaf X) hS b (hnext _)

theorem cohomologyDimension_eq_of_quotient_vanishing
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (n : ℕ) (hprev : ∀ z : cohomology S.X₃ n, z = 0)
    (hnext : ∀ z : cohomology S.X₃ (n+1), z = 0) :
    cohomologyDimension p S.X₁ (n+1) = cohomologyDimension p S.X₂ (n+1) := by
  let := Module.compHom (cohomology S.X₁ (n+1)) (baseScalars p)
  let := Module.compHom (cohomology S.X₂ (n+1)) (baseScalars p)
  exact (LinearEquiv.ofBijective (cohomologyMap p S.f (n+1))
    (cohomologyMap_bijective_of_quotient_vanishing p S hS n hprev hnext)).finrank_eq

theorem eventual_cohomologyDimension_constant_of_two_sequences
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (F B Q R : ℕ → X.Modules)
    (f : ∀ n, F n ⟶ B n) (g : ∀ n, B n ⟶ Q n)
    (f' : ∀ n, F (n+1) ⟶ B n) (g' : ∀ n, B n ⟶ R n)
    (hcomp : ∀ n, f n ≫ g n = 0) (hcomp' : ∀ n, f' n ≫ g' n = 0)
    (hshort : ∀ n, (ShortComplex.mk (f n) (g n) (hcomp n)).ShortExact)
    (hshort' : ∀ n, (ShortComplex.mk (f' n) (g' n) (hcomp' n)).ShortExact)
    (q : ℕ)
    (hzero : ∃ N, ∀ n, N ≤ n →
      (∀ z : cohomology (Q n) q, z = 0) ∧
      (∀ z : cohomology (Q n) (q+1), z = 0) ∧
      (∀ z : cohomology (R n) q, z = 0) ∧
      (∀ z : cohomology (R n) (q+1), z = 0)) :
    ∃ N, ∀ n, N ≤ n → cohomologyDimension p (F n) (q+1) =
      cohomologyDimension p (F N) (q+1) := by
  obtain ⟨N,hN⟩ := hzero
  have hstep (n : ℕ) (hn : N ≤ n) :
      cohomologyDimension p (F n) (q+1) = cohomologyDimension p (F (n+1)) (q+1) := by
    obtain ⟨hQ₀,hQ₁,hR₀,hR₁⟩ := hN n hn
    exact (cohomologyDimension_eq_of_quotient_vanishing p _ (hshort n) q hQ₀ hQ₁).trans
      (cohomologyDimension_eq_of_quotient_vanishing p _ (hshort' n) q hR₀ hR₁).symm
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero => simp
  | succ k ih =>
    exact (hstep (N+k) (by omega)).symm.trans (ih (by omega))

end
end PiExponent.NumericalAmpleness

end OAI
