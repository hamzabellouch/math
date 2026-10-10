import Mathlib
import OAI.Algebra.FrobeniusObstruction.Obstruction
import OAI.Algebra.AlgebraicObstruction.FormalArcs

namespace OAI

noncomputable section
open scoped BigOperators

namespace BoundaryOnly.FormalObstruction.AlgebraicReplacement.FormalArc
open IsLocalRing
open scoped nonZeroDivisors

private theorem radical_eq_maximal_of_minimal {S : Type*} [CommRing S]
    [IsLocalRing S] (I : Ideal S)
    (h : maximalIdeal S ∈ I.minimalPrimes) : I.radical = maximalIdeal S := by
  apply le_antisymm
  · exact (Ideal.IsPrime.radical_le_iff (inferInstance : (maximalIdeal S).IsPrime)).mpr h.1.2
  · rw [← Ideal.sInf_minimalPrimes]
    apply le_sInf
    intro p hp
    exact h.2 hp.1 (le_maximalIdeal hp.1.1.ne_top)

variable {S : Type*} [CommRing S] [IsDomain S] [IsLocalRing S] [IsNoetherianRing S]

theorem exists_primary_curve_quotient (b : S) (hb : b ≠ 0)
    (hbm : b ∈ maximalIdeal S) :
    ∃ p : Ideal S, p.IsPrime ∧ b ∉ p ∧
      (Ideal.span {b} ⊔ p).radical = maximalIdeal S := by
  classical
  let B : Ideal S := Ideal.span {b}
  have hB : B ≤ maximalIdeal S := (Ideal.span_singleton_le_iff_mem _).mpr hbm
  have hBne : B ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal S).ne_top hB
  let Q := S ⧸ B
  have : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr hBne
  let q : S →+* Q := Ideal.Quotient.mk B
  have hsurj : Function.Surjective q := Ideal.Quotient.mk_surjective
  have : IsLocalRing Q := IsLocalRing.of_surjective' q hsurj
  have : IsLocalHom q := IsLocalHom.of_surjective q hsurj
  obtain ⟨s,hs,hcard⟩ :=
    Ideal.exists_finset_card_eq_height_of_isNoetherianRing (maximalIdeal Q)
  have hrad : (Ideal.span (s : Set Q)).radical = maximalIdeal Q :=
    radical_eq_maximal_of_minimal _ hs
  let lift : Q → S := Function.surjInv hsurj
  have hlift (x : Q) : q (lift x) = x := Function.surjInv_eq hsurj x
  let t : Finset S := s.image lift
  let J : Ideal S := Ideal.span (t : Set S)
  have hmap : J.map q = Ideal.span (s : Set Q) := by
    rw [Ideal.map_span]
    congr 1
    ext x
    simp only [t,Finset.coe_image,Set.mem_image]
    constructor
    · rintro ⟨y,⟨z,hz,rfl⟩,rfl⟩
      simpa only [hlift] using hz
    · intro hx
      exact ⟨lift x,⟨x,hx,rfl⟩,hlift x⟩
  have hJB : (J ⊔ B).radical = maximalIdeal S := by
    have heq := congrArg (Ideal.comap q) hrad
    rw [← hmap,Ideal.comap_radical,Ideal.comap_map_of_surjective q hsurj] at heq
    have hker : RingHom.ker q = B := Ideal.mk_ker
    rw [RingHom.ker_eq_comap_bot] at hker
    rw [hker,maximalIdeal_comap q] at heq
    exact heq
  have hJm : J ≤ maximalIdeal S :=
    (le_sup_left : J ≤ J ⊔ B).trans (Ideal.le_radical.trans hJB.le)
  obtain ⟨p,hp,hpm⟩ := Ideal.exists_minimalPrimes_le hJm
  have : p.IsPrime := hp.1.1
  have hheight : p.height < (maximalIdeal S).height := by
    have hd := ringKrullDim_quotient_succ_le_of_nonZeroDivisor
      ((mem_nonZeroDivisors_iff_ne_zero).mpr hb)
    rw [← maximalIdeal_height_eq_ringKrullDim (R := Q),
      ← maximalIdeal_height_eq_ringKrullDim (R := S)] at hd
    have hd' : (maximalIdeal Q).height + 1 ≤ (maximalIdeal S).height := by
      exact_mod_cast hd
    have hc : (s.card : ℕ∞) + 1 ≤ (maximalIdeal S).height := by rwa [hcard]
    have hcs : (s.card : ℕ∞) < (s.card : ℕ∞) + 1 := by
      exact_mod_cast Nat.lt_succ_self s.card
    exact lt_of_le_of_lt (Ideal.height_le_card_of_mem_minimalPrimes_span_finset hp)
      (lt_of_le_of_lt (by exact_mod_cast Finset.card_image_le (s := s) (f := lift))
        (hcs.trans_le hc))
  have hbp : b ∉ p := by
    intro h
    have hBp : B ≤ p := (Ideal.span_singleton_le_iff_mem _).mpr h
    have hmp : maximalIdeal S ≤ p := by
      rw [← hJB]
      exact (Ideal.IsPrime.radical_le_iff (inferInstance : p.IsPrime)).mpr
        (sup_le hp.1.2 hBp)
    have heq := le_antisymm hpm hmp
    exact (ne_of_lt hheight) (congrArg Ideal.height heq)
  refine ⟨p,inferInstance,hbp,?_⟩
  apply le_antisymm
  · exact (Ideal.IsPrime.radical_le_iff (inferInstance : (maximalIdeal S).IsPrime)).mpr (sup_le hB hpm)
  · rw [← hJB]
    exact Ideal.radical_mono (sup_le (hp.1.2.trans le_sup_right) le_sup_left)

end BoundaryOnly.FormalObstruction.AlgebraicReplacement.FormalArc

namespace BoundaryOnly.FormalObstruction.AlgebraicReplacement.FormalArc
open IsLocalRing

private instance quotient_localRing {R : Type*} [CommRing R] [IsLocalRing R]
    (J : Ideal R) [Nontrivial (R ⧸ J)] : IsLocalRing (R ⧸ J) :=
  IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective

variable {S : Type*} [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
  [IsAdicComplete (maximalIdeal S) S]

theorem local_quotient_complete (J : Ideal S) [Nontrivial (S ⧸ J)] :
    IsAdicComplete (maximalIdeal (S ⧸ J)) (S ⧸ J) := by
  let m := maximalIdeal S
  let Q := S ⧸ J
  let f : S →ₗ[S] Q := J.mkQ
  have hf : Function.Surjective f := J.mkQ_surjective
  have : IsPrecomplete m Q := by
    apply (AdicCompletion.of_surjective_iff (I := m) (M := Q)).mp
    intro z
    obtain ⟨x,hx⟩ := AdicCompletion.map_surjective_of_mkQ_comp_surjective
      (I := m) (f := f) ((Submodule.mkQ_surjective (m • ⊤)).comp hf) z
    obtain ⟨y,hy⟩ := AdicCompletion.of_surjective m S x
    refine ⟨f y,?_⟩
    rw [← AdicCompletion.map_of,hy,hx]
  have : IsAdicComplete m Q := { }
  have hm : m.map (algebraMap S Q) = maximalIdeal Q :=
    map_maximalIdeal_of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  rw [← hm]
  exact (IsAdicComplete.map_algebraMap_iff m Q).mpr inferInstance

omit [IsNoetherianRing S] [IsAdicComplete (maximalIdeal S) S] in

theorem quotient_residue_surjective {K : Type*} [Field K] [Algebra K S]
    (J : Ideal S) [Nontrivial (S ⧸ J)]
    (hres : Function.Surjective
      ((Ideal.Quotient.mk (maximalIdeal S)).comp (algebraMap K S))) :
    Function.Surjective
      ((Ideal.Quotient.mk (maximalIdeal (S ⧸ J))).comp (algebraMap K (S ⧸ J))) := by
  let Q := S ⧸ J
  let q : S →+* Q := Ideal.Quotient.mk J
  have : IsLocalHom q := IsLocalHom.of_surjective q Ideal.Quotient.mk_surjective
  intro z
  obtain ⟨y,hy⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨x,hx⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨c,hc⟩ := hres (residue S x)
  refine ⟨c,?_⟩
  have hc' := congrArg (ResidueField.map q) hc
  change ResidueField.map q (residue S (algebraMap K S c)) =
    ResidueField.map q (residue S x) at hc'
  rw [ResidueField.map_residue,ResidueField.map_residue] at hc'
  change residue Q (algebraMap K Q c) = z
  change q x = y at hx
  change residue Q y = z at hy
  rw [hx,hy] at hc'
  exact hc'

end BoundaryOnly.FormalObstruction.AlgebraicReplacement.FormalArc

namespace BoundaryOnly.FormalObstruction.AlgebraicReplacement.FormalArc
open IsLocalRing
variable {K S : Type*} [Field K] [IsAlgClosed K] [CharZero K]
  [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
  [Algebra K S] [IsAdicComplete (maximalIdeal S) S]

theorem domain_detecting_arc [IsDomain S] (b : S) (hb : b ≠ 0)
    (hbm : b ∈ maximalIdeal S)
    (hres : Function.Surjective
      ((Ideal.Quotient.mk (maximalIdeal S)).comp (algebraMap K S))) :
    ∃ f : S →ₐ[K] PowerSeries K, IsLocalHom f.toRingHom ∧ f b ≠ 0 := by
  obtain ⟨p,hp,hbp,hprimary⟩ := exists_primary_curve_quotient b hb hbm
  have : Ideal.IsPrime p := hp
  let Q := S ⧸ p
  let q : S →ₐ[K] Q := Ideal.Quotient.mkₐ K p
  have hsurj : Function.Surjective q := Ideal.Quotient.mk_surjective
  have : IsLocalHom q.toRingHom := IsLocalHom.of_surjective _ hsurj
  have : IsAdicComplete (maximalIdeal Q) Q := local_quotient_complete p
  have hqb : q b ≠ 0 := fun h ↦ hbp (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hprimaryQ : (Ideal.span {q b}).radical = maximalIdeal Q := by
    have h := congrArg (Ideal.map q.toRingHom) hprimary
    have hker : RingHom.ker q.toRingHom ≤ Ideal.span {b} ⊔ p := by
      change RingHom.ker (Ideal.Quotient.mk p) ≤ _
      rw [Ideal.mk_ker]
      exact le_sup_right
    rw [Ideal.map_radical_of_surjective hsurj hker,Ideal.map_sup,
      Ideal.map_span,Set.image_singleton] at h
    have hpmap : p.map q.toRingHom = ⊥ := Ideal.map_quotient_self p
    rw [hpmap,sup_bot_eq,
      map_maximalIdeal_of_surjective q.toRingHom hsurj] at h
    exact h
  obtain ⟨g,hginj,hglocal⟩ := primary_parameter_arc (q b) hqb hprimaryQ
    (quotient_residue_surjective p hres)
  have : IsLocalHom g.toRingHom := hglocal
  refine ⟨g.comp q,?_,?_⟩
  · change IsLocalHom (g.toRingHom.comp q.toRingHom)
    infer_instance
  · change g (q b) ≠ 0
    exact fun h ↦ hqb (hginj (h.trans (map_zero g).symm))

theorem reduced_detecting_arc [IsReduced S] (b : S) (hb : b ≠ 0)
    (hbm : b ∈ maximalIdeal S)
    (hres : Function.Surjective
      ((Ideal.Quotient.mk (maximalIdeal S)).comp (algebraMap K S))) :
    ∃ f : S →ₐ[K] PowerSeries K, IsLocalHom f.toRingHom ∧ f b ≠ 0 := by
  have hnil : b ∉ nilradical S := by
    intro h
    exact hb (IsReduced.eq_zero b (mem_nilradical.mp h))
  rw [nilradical_eq_sInf,Submodule.mem_sInf] at hnil
  push Not at hnil
  obtain ⟨p,hp,hbp⟩ := hnil
  have : Ideal.IsPrime p := hp
  let Q := S ⧸ p
  let q : S →ₐ[K] Q := Ideal.Quotient.mkₐ K p
  have hsurj : Function.Surjective q := Ideal.Quotient.mk_surjective
  have : IsLocalHom q.toRingHom := IsLocalHom.of_surjective _ hsurj
  have : IsAdicComplete (maximalIdeal Q) Q := local_quotient_complete p
  have hqb : q b ≠ 0 := fun h ↦ hbp (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hqbm : q b ∈ maximalIdeal Q := map_nonunit q.toRingHom b hbm
  obtain ⟨g,hglocal,hgb⟩ := domain_detecting_arc (q b) hqb hqbm
    (quotient_residue_surjective p hres)
  have : IsLocalHom g.toRingHom := hglocal
  refine ⟨g.comp q,?_,hgb⟩
  change IsLocalHom (g.toRingHom.comp q.toRingHom)
  infer_instance

end BoundaryOnly.FormalObstruction.AlgebraicReplacement.FormalArc

namespace BoundaryOnly.FormalObstruction.AlgebraicReplacement.FormalArc
open IsLocalRing
variable {K S : Type*} [Field K] [IsAlgClosed K] [CharZero K]
  [CommRing S] [IsLocalRing S] [IsNoetherianRing S] [IsReduced S]
  [Algebra K S] [IsAdicComplete (maximalIdeal S) S]

theorem reduced_detecting_continuous_arc (b : S) (hb : b ≠ 0)
    (hbm : b ∈ maximalIdeal S)
    (hres : Function.Surjective
      ((Ideal.Quotient.mk (maximalIdeal S)).comp (algebraMap K S))) :
    letI : WithIdeal S := ⟨maximalIdeal S⟩
    letI : WithIdeal (PowerSeries K) := ⟨maximalIdeal (PowerSeries K)⟩
    ∃ f : S →ₐ[K] PowerSeries K, IsLocalHom f.toRingHom ∧
      Continuous f ∧ f b ≠ 0 := by
  let : WithIdeal S := ⟨maximalIdeal S⟩
  let : WithIdeal (PowerSeries K) := ⟨maximalIdeal (PowerSeries K)⟩
  obtain ⟨f,hf,hfb⟩ := reduced_detecting_arc b hb hbm hres
  have : IsLocalHom f.toRingHom := hf
  refine ⟨f,hf,?_,hfb⟩
  exact (WithIdeal.uniformContinuous_of_map_le (f := f.toRingHom)
    (map_maximalIdeal_le f.toRingHom)).continuous
end BoundaryOnly.FormalObstruction.AlgebraicReplacement.FormalArc

namespace BoundaryOnly.FormalObstruction.AlgebraicReplacement.FormalArc
open MvPowerSeries IsLocalRing
variable {σ K : Type*} [Finite σ] [Field K]

lemma polynomial_approximate (f : MvPowerSeries σ K) (n : ℕ) :
    ∃ p : MvPolynomial σ K, f - (p : MvPowerSeries σ K) ∈
      (Ideal.span (Set.range (X : σ → MvPowerSeries σ K))) ^ n := by
  let J := MvPolynomial.idealOfVars σ K
  let e := toAdicCompletionAlgEquiv σ K
  have hmap : Ideal.map e.toRingHom (Ideal.span (Set.range X)) =
      J.map (algebraMap (MvPolynomial σ K) (AdicCompletion J (MvPolynomial σ K))) := by
    change Ideal.map e.toRingHom (Ideal.span (Set.range X)) =
      (MvPolynomial.idealOfVars σ K).map _
    simp_rw [MvPolynomial.idealOfVars,Ideal.map_span, ← Set.range_comp]
    congr 2; ext1
    simp [e,J,AdicCompletion.algebraMap_apply, ← MvPolynomial.coe_X, toAdicCompletion_coe]
  obtain ⟨p,hp⟩ := Submodule.Quotient.mk_surjective (J^n • (⊤ : Ideal (MvPolynomial σ K)))
    ((e f).val n)
  refine ⟨p,?_⟩
  have he : e (f - (p : MvPowerSeries σ K)) ∈
      (Ideal.span (Set.range X) ^ n).map e.toRingHom := by
    rw [Ideal.map_pow,hmap,← Ideal.map_pow,← Submodule.restrictScalars_mem (MvPolynomial σ K),
      ← Ideal.smul_top_eq_map,AdicCompletion.pow_smul_top_eq_ker_eval J.fg_of_isNoetherianRing]
    change AdicCompletion.eval J (MvPolynomial σ K) n (e (f - (p : MvPowerSeries σ K))) = 0
    rw [map_sub]
    have hecoe : e (p : MvPowerSeries σ K) = AdicCompletion.of J (MvPolynomial σ K) p :=
      toAdicCompletion_coe p
    rw [hecoe]
    rw [map_sub,AdicCompletion.eval_of]
    exact sub_eq_zero.mpr hp.symm
  obtain ⟨z,hz,hze⟩ := (Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective).mp he
  exact e.injective hze ▸ hz

lemma span_variables_eq_constant_kernel :
    Ideal.span (Set.range (X : σ → MvPowerSeries σ K)) =
      RingHom.ker (constantCoeff (σ := σ) (R := K)) := by
  have hle : Ideal.span (Set.range (X : σ → MvPowerSeries σ K)) ≤
      RingHom.ker (constantCoeff (σ := σ) (R := K)) := by
    rw [Ideal.span_le]
    rintro _ ⟨i,rfl⟩
    simp
  apply le_antisymm hle
  intro f hf
  obtain ⟨p,hp⟩ := polynomial_approximate f 1
  rw [pow_one] at hp
  have hpc : MvPolynomial.constantCoeff p = 0 := by
    have hh := hle hp
    change constantCoeff (f - (p : MvPowerSeries σ K)) = 0 at hh
    change constantCoeff f = 0 at hf
    rw [map_sub,hf,zero_sub,neg_eq_zero] at hh
    exact hh
  have hpvar : p ∈ MvPolynomial.idealOfVars σ K := by
    rw [← pow_one (MvPolynomial.idealOfVars σ K),MvPolynomial.mem_pow_idealOfVars_iff']
    intro d hd
    have hd0 : d = 0 := (Finsupp.degree_eq_zero_iff d).mp (by omega)
    subst d
    exact hpc
  have hpcoe : (p : MvPowerSeries σ K) ∈ Ideal.span (Set.range X) := by
    have hh := Ideal.mem_map_of_mem (MvPolynomial.coeToMvPowerSeries.ringHom :
      MvPolynomial σ K →+* MvPowerSeries σ K) hpvar
    have hm : Ideal.map (MvPolynomial.coeToMvPowerSeries.ringHom :
        MvPolynomial σ K →+* MvPowerSeries σ K) (MvPolynomial.idealOfVars σ K) =
        Ideal.span (Set.range X) := by
      rw [MvPolynomial.idealOfVars,Ideal.map_span,← Set.range_comp]
      simp only [Function.comp_def,MvPolynomial.coeToMvPowerSeries.ringHom_apply,MvPolynomial.coe_X]
    rw [hm] at hh
    exact hh
  simpa only [sub_add_cancel] using Ideal.add_mem _ hp hpcoe

lemma maximalIdeal_eq_variables :
    maximalIdeal (MvPowerSeries σ K) = Ideal.span (Set.range X) := by
  rw [span_variables_eq_constant_kernel]
  ext f
  change ¬IsUnit f ↔ constantCoeff f = 0
  rw [MvPowerSeries.isUnit_iff_constantCoeff]
  simp only [isUnit_iff_ne_zero,not_not]

instance complete_mps_maximal :
    IsAdicComplete (maximalIdeal (MvPowerSeries σ K)) (MvPowerSeries σ K) := by
  rw [maximalIdeal_eq_variables]
  infer_instance

lemma residue_mps_surjective : Function.Surjective
    ((Ideal.Quotient.mk (maximalIdeal (MvPowerSeries σ K))).comp
      (algebraMap K (MvPowerSeries σ K))) := by
  intro z
  obtain ⟨f,rfl⟩ := Ideal.Quotient.mk_surjective z
  refine ⟨constantCoeff f,?_⟩
  change Ideal.Quotient.mk _ (C (constantCoeff f)) = Ideal.Quotient.mk _ f
  rw [Ideal.Quotient.eq,maximalIdeal_eq_variables,span_variables_eq_constant_kernel]
  simp

theorem local_mps_hom_ext {T : Type*} [CommRing T] [IsLocalRing T]
    [Algebra K T] [IsHausdorff (maximalIdeal T) T]
    (f g : MvPowerSeries σ K →ₐ[K] T)
    [IsLocalHom f.toRingHom] [IsLocalHom g.toRingHom]
    (hX : ∀ i, f (X i) = g (X i)) : f = g := by
  have hpoly : f.comp (MvPolynomial.coeToMvPowerSeries.algHom K) =
      g.comp (MvPolynomial.coeToMvPowerSeries.algHom K) := by
    apply MvPolynomial.algHom_ext
    intro i
    simpa using hX i
  apply AlgHom.ext
  intro x
  rw [IsHausdorff.eq_iff_smodEq (I := maximalIdeal T)]
  intro n
  obtain ⟨p,hp⟩ := polynomial_approximate x n
  rw [← maximalIdeal_eq_variables] at hp
  have hf := Ideal.mem_map_of_mem f.toRingHom hp
  have hg := Ideal.mem_map_of_mem g.toRingHom hp
  rw [Ideal.map_pow] at hf hg
  have hf' := (pow_le_pow_left' (map_maximalIdeal_le f.toRingHom) n) hf
  have hg' := (pow_le_pow_left' (map_maximalIdeal_le g.toRingHom) n) hg
  have hph : f (p : MvPowerSeries σ K) = g (p : MvPowerSeries σ K) :=
    by simpa using AlgHom.congr_fun hpoly p
  rw [SModEq.sub_mem,smul_eq_mul,Ideal.mul_top]
  have hh := Ideal.sub_mem _ hf' hg'
  simp only [map_sub] at hh
  change (f x - f (p : MvPowerSeries σ K)) -
    (g x - g (p : MvPowerSeries σ K)) ∈ maximalIdeal T ^ n at hh
  simpa only [hph,sub_sub_sub_cancel_right] using hh

end BoundaryOnly.FormalObstruction.AlgebraicReplacement.FormalArc

end

end OAI
