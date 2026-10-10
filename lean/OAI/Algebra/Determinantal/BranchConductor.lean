import OAI.Algebra.Determinantal.LocalDerivations

namespace OAI
namespace PermanentBorder.ReducedBranchConductor
open Polynomial

section Ideal
variable {S : Type*} [CommRing S]
noncomputable def gradientIdeal (f b c d : S[X]) (x : S) : Ideal S[X] :=
  Ideal.span {f, b^2+X*d^2,c^2+C x*d^2}
noncomputable def enlargedGradientIdeal (f b c d : S[X]) (x : S) : Ideal S[X] :=
  gradientIdeal f b c d x ⊔ Ideal.span {d^2} * (gradientIdeal f b c d x).radical

variable {B : Type*} [CommRing B] [Algebra S B]
lemma map_enlarged_le (f b c d : S[X]) (x : S) (y : B) (J : Ideal B)
    (hf : aeval y f = 0)
    (hb : aeval y (b^2+X*d^2) ∈ J)
    (hc : aeval y (c^2+C x*d^2) ∈ J)
    (hr : ∀ z ∈ (Ideal.span {aeval y (b^2+X*d^2),aeval y (c^2+C x*d^2)}).radical,
      (aeval y d)^2*z ∈ J) :
    enlargedGradientIdeal f b c d x ≤ Ideal.comap (aeval y) J := by
  let H : Ideal B := Ideal.span {aeval y (b^2+X*d^2),aeval y (c^2+C x*d^2)}
  have hi : gradientIdeal f b c d x ≤ Ideal.comap (aeval y) H := by
    apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hz
    rcases hz with hz|hz|hz
    · rw [hz]
      change aeval y f ∈ H
      rw [hf]; exact H.zero_mem
    · rw [hz]; exact Ideal.subset_span (by simp)
    · rw [hz]; exact Ideal.subset_span (by simp)
  have hir : (gradientIdeal f b c d x).radical ≤ Ideal.comap (aeval y) H.radical := by
    rw [Ideal.comap_radical]
    exact Ideal.radical_mono hi
  apply sup_le
  · apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hz
    rcases hz with hz|hz|hz
    · rw [hz]
      change aeval y f ∈ J
      rw [hf]; exact J.zero_mem
    · rw [hz]; exact hb
    · rw [hz]; exact hc
  · rw [Ideal.span_singleton_mul_le_iff]
    intro z hz
    change aeval y (d^2*z) ∈ J
    rw [map_mul,map_pow]
    exact hr _ (hir hz)
end Ideal

section Field
variable {Q : Type*} [Field Q]
lemma root_generates (p : Q[X]) : Algebra.adjoin Q {AdjoinRoot.root p} = ⊤ := by
  rw [Algebra.adjoin_singleton_eq_range_aeval,AlgHom.range_eq_top]
  intro z
  obtain ⟨q,hq⟩ := AdjoinRoot.mk_surjective z
  exact ⟨q,by rw [AdjoinRoot.aeval_eq]; exact hq⟩

lemma root_separable (p : Q[X]) [Fact (Irreducible p)] (hsep : p.Separable) :
    Algebra.IsSeparable Q (AdjoinRoot p) := by
  have hp0 : p ≠ 0 := (Fact.out : Irreducible p).ne_zero
  have hr : IsSeparable Q (AdjoinRoot.root p) := hsep.of_dvd
    (minpoly.dvd Q _ (AdjoinRoot.eval₂_root p))
  have hl : Algebra.adjoin Q {AdjoinRoot.root p} ≤ (separableClosure Q (AdjoinRoot p)).toSubalgebra :=
    Algebra.adjoin_le (by intro z hz; obtain rfl := Set.mem_singleton_iff.mp hz; exact hr)
  rw [root_generates] at hl
  exact ⟨fun z => hl (show z ∈ (⊤ : Subalgebra Q (AdjoinRoot p)) from trivial)⟩
end Field

section Realization
variable {K S Q : Type*} [CommRing K] [CommRing S] [IsDomain S]
  [IsPrincipalIdealRing S] [IsLocalRing S] [IsAlgClosed (IsLocalRing.ResidueField S)]
  [Algebra K S] [CharP S 2]
  [Field Q] [Algebra S Q] [IsFractionRing S Q]

include K in

theorem irreducible_realization (δ : Derivation K S S) (x : S) (hx : δ x=1)
    (f p w a b c d : S[X]) (hp : p.Monic)
    (hir : Irreducible (p.map (algebraMap S Q)))
    (hfactor : f=p*w) (hsep : (f.map (algebraMap S Q)).Separable)
    (hsq : f=a^2+C x*b^2+X*c^2+C x*X*d^2)
    (hder : f.derivative=c^2+C x*d^2)
    (z : S[X]) (hz : z ∈ enlargedGradientIdeal f b c d x)
    (t : AdjoinRoot (p.map (algebraMap S Q))) (ht : IsIntegral S t) :
    ∃ q : S[X], AdjoinRoot.mk (p.map (algebraMap S Q)) ((w*q).map (algebraMap S Q)) =
      AdjoinRoot.mk (p.map (algebraMap S Q)) (z.map (algebraMap S Q))*t := by
  let pg := p.map (algebraMap S Q)
  let : Fact (Irreducible pg) := ⟨hir⟩
  let L := AdjoinRoot pg
  let B := integralClosure S L
  let : Algebra K B := Algebra.compHom B (algebraMap K S)
  let : IsScalarTower K S B := IsScalarTower.of_algebraMap_eq' rfl
  have hps : pg.Separable := hsep.of_dvd (Polynomial.map_dvd _ (hfactor ▸ dvd_mul_right p w))
  let : Algebra.IsSeparable Q L := root_separable pg hps
  let : FiniteDimensional Q L := (AdjoinRoot.powerBasis hir.ne_zero).finite
  let : IsDedekindDomain B := integralClosure.isDedekindDomain S Q L
  let : Module.Finite S B := IsIntegralClosure.finite S Q L B
  let : IsPrincipalIdealRing B := Conductor.integralClosure_isPrincipalIdealRing (S := S) (Q := Q) (L := L)
  have hsL : Function.Injective (algebraMap S L) := by
    rw [IsScalarTower.algebraMap_eq S Q L]
    exact (algebraMap Q L).injective.comp (IsFractionRing.injective S Q)
  have hsB : Function.Injective (algebraMap S B) := by
    intro a b h
    apply hsL
    simpa only [IsScalarTower.algebraMap_apply S B L] using congrArg (algebraMap B L) h
  let : CharP B 2 := charP_of_injective_algebraMap hsB 2
  let : Module.IsTorsionFree S B := (Module.isTorsionFree_iff_algebraMap_injective).mpr hsB
  have hyi : IsIntegral S (AdjoinRoot.root pg) := ⟨p,hp,by
    change aeval (AdjoinRoot.root pg) p = 0
    rw [AdjoinRoot.aeval_eq_of_algebra]
    exact AdjoinRoot.mk_self⟩
  let y : B := IsIntegralClosure.mk' B (AdjoinRoot.root pg) hyi
  have hy : algebraMap B L y = AdjoinRoot.root pg := IsIntegralClosure.algebraMap_mk' B _ hyi
  have hyint : IsIntegral S y := IsIntegralClosure.isIntegral S L y
  have hmin : minpoly S y = p := by
    apply Polynomial.map_injective _ (IsFractionRing.injective S Q)
    rw [← minpoly.isIntegrallyClosed_eq_field_fractions Q L hyint,hy,
      AdjoinRoot.minpoly_root hir.ne_zero,(hp.map _).leadingCoeff,inv_one,C_1,mul_one]
  have hygen : Algebra.adjoin Q {algebraMap B L y} = ⊤ := by rw [hy]; exact root_generates pg
  have hfy : aeval y f = 0 := by rw [hfactor,← hmin,map_mul,minpoly.aeval,zero_mul]
  have hsq' : (aeval y a)^2+algebraMap S B x*(aeval y b)^2+y*(aeval y c)^2+
      algebraMap S B x*y*(aeval y d)^2=0 := by
    simpa only [hsq,map_add,map_mul,map_pow,aeval_C,aeval_X] using hfy
  obtain ⟨hb,hc,hr⟩ := branch_conductor (Q := Q) (L := L) δ x hx y
    (aeval y a) (aeval y b) (aeval y c) (aeval y d) f w hygen
    (by rw [hmin]; exact hfactor) hsep (by simp only [hder,map_add,map_mul,map_pow,aeval_C]) hsq'
  have hm : aeval y z ∈ conductor S y * Ideal.span {aeval y w} := by
    change z ∈ Ideal.comap (aeval y) (conductor S y * Ideal.span {aeval y w})
    apply map_enlarged_le f b c d x y _ hfy ?_ ?_ ?_ hz
    · simpa only [map_add,map_mul,map_pow,aeval_X] using hb
    · simpa only [map_add,map_mul,map_pow,aeval_C] using hc
    · simpa only [map_add,map_mul,map_pow,aeval_X,aeval_C] using hr
  obtain ⟨u,hu,he⟩ := Ideal.mem_mul_span_singleton.mp hm
  let t' : B := IsIntegralClosure.mk' B t ht
  have hur := mem_conductor_iff.mp hu t'
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hur
  obtain ⟨q,hq⟩ := hur
  change aeval y q = u*t' at hq
  refine ⟨q,?_⟩
  have hzb : aeval y (w*q) = aeval y z*t' := by
    rw [map_mul,hq,← he]
    ring
  have hh := congrArg (algebraMap B L) hzb
  have hev (v : S[X]) : algebraMap B L (aeval y v) =
      AdjoinRoot.mk pg (v.map (algebraMap S Q)) := by
    change (IsScalarTower.toAlgHom S B L) (aeval y v) = _
    rw [← aeval_algHom_apply]
    change aeval (algebraMap B L y) v = _
    rw [hy,AdjoinRoot.aeval_eq_of_algebra]
  rw [map_mul (algebraMap B L),hev,hev,IsIntegralClosure.algebraMap_mk'] at hh
  exact hh
end Realization
end PermanentBorder.ReducedBranchConductor
namespace PermanentBorder.FactorNormalization
open Polynomial UniqueFactorizationMonoid
variable {S Q : Type*} [CommRing S] [IsDomain S] [IsIntegrallyClosed S]
  [Field Q] [Algebra S Q] [IsFractionRing S Q]

omit [IsDomain S] in

lemma lift_monic_factor {f : S[X]} (hf : f.Monic) {p : Q[X]}
    (hp : p.Monic) (hd : p ∣ (f).map (algebraMap S Q)) :
    ∃ q : S[X], q.Monic ∧ q.map (algebraMap S Q) = p := by
  obtain ⟨q,hq⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd Q hf hd
  rw [hp.leadingCoeff,C_1,mul_one] at hq
  exact ⟨q,Polynomial.monic_of_injective (IsFractionRing.injective S Q)
    (hq ▸ hp),hq⟩

omit [IsDomain S] in

theorem exists_factors {f : S[X]} (hf : f.Monic)
    (hsep : ((f).map (algebraMap S Q)).Separable) :
    ∃ (s : Finset Q[X]) (p : s → S[X]),
      (∀ i, (p i).Monic ∧ (p i).map (algebraMap S Q) = i.val ∧ Irreducible i.val) ∧
      (∏ i, p i) = f := by
  classical
  let g := (f).map (algebraMap S Q)
  have hg : g.Monic := hf.map _
  let s : Finset Q[X] := ⟨normalizedFactors g,
    (squarefree_iff_nodup_normalizedFactors hg.ne_zero).mp hsep.squarefree⟩
  have hi (i : s) : Irreducible i.val ∧ i.val.Monic ∧ i.val ∣ g :=
    (Polynomial.mem_normalizedFactors_iff hg.ne_zero).mp i.property
  choose p hpm hpe using fun i : s => lift_monic_factor hf (hi i).2.1 (hi i).2.2
  refine ⟨s,p,fun i => ⟨hpm i,hpe i,(hi i).1⟩,?_⟩
  apply Polynomial.map_injective _ (IsFractionRing.injective S Q)
  rw [Polynomial.map_prod]
  simp_rw [hpe]
  have hp := leadingCoeff_mul_prod_normalizedFactors g
  rw [hg.leadingCoeff,C_1,one_mul] at hp
  change (∏ i : s, id (i : Q[X])) = g
  rw [Finset.prod_coe_sort]
  change ((normalizedFactors g).map id).prod = g
  simpa using hp

section Cofactors
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (p : ι → S[X])
noncomputable def cofactor (i : ι) : S[X] := ∏ j ∈ Finset.univ.erase i, p j

omit [IsDomain S] [IsIntegrallyClosed S] in
lemma factor_mul_cofactor (i : ι) : p i * cofactor p i = ∏ j, p j := by
  classical
  exact Finset.mul_prod_erase Finset.univ p (Finset.mem_univ i)

omit [IsDomain S] [IsIntegrallyClosed S] in
lemma cofactor_dvd_of_ne {i j : ι} (h : i ≠ j) : p j ∣ cofactor p i := by
  classical
  apply Finset.dvd_prod_of_mem
  simp only [Finset.mem_erase,Finset.mem_univ,and_true]
  exact h.symm

end Cofactors
end PermanentBorder.FactorNormalization

namespace PermanentBorder.FactorNormalization
open Polynomial
section Reconstruct
variable {S Q ι : Type*} [CommRing S] [Field Q] [Algebra S Q]
  [Fintype ι] [DecidableEq ι]
variable (p : ι → S[X])
local notation "f" => ∏ i, p i
local notation "pQ" => fun i => Polynomial.map (algebraMap S Q) (p i)

noncomputable def component (i : ι) :
    AdjoinRoot ((f).map (algebraMap S Q)) →ₐ[Q] AdjoinRoot (pQ i) :=
  AdjoinRoot.algHomOfDvd Q _ _ (map_dvd (algebraMap S Q)
    (Finset.dvd_prod_of_mem p (Finset.mem_univ i)))

omit [DecidableEq ι] in
@[simp] lemma component_mk (i : ι) (q : Q[X]) :
    component p i (AdjoinRoot.mk ((f).map (algebraMap S Q)) q) =
      AdjoinRoot.mk (pQ i) q := by
  change (AdjoinRoot.algHomOfDvd Q _ _ _) _ = _
  rw [← AdjoinRoot.aeval_eq,← aeval_algHom_apply,AdjoinRoot.algHomOfDvd_root,AdjoinRoot.aeval_eq]

omit [DecidableEq ι] in
lemma components_injective
    (hcop : Pairwise (fun i j => IsCoprime (pQ i) (pQ j))) :
    Function.Injective (fun z => fun i => component (Q := Q) p i z) := by
  intro z w h
  have hz : ∀ i, component p i (z-w) = 0 := by
    intro i
    rw [map_sub,sub_eq_zero]
    exact congrFun h i
  suffices z-w=0 from sub_eq_zero.mp this
  obtain ⟨q,hq⟩ := AdjoinRoot.mk_surjective (z-w)
  rw [← hq,AdjoinRoot.mk_eq_zero]
  rw [Polynomial.map_prod]
  apply Finset.prod_dvd_of_coprime
  · intro i _ j _ hij
    exact hcop hij
  · intro i _
    apply AdjoinRoot.mk_eq_zero.mp
    simpa only [← hq,component_mk] using hz i

theorem reconstruct (hcop : Pairwise (fun i j => IsCoprime (pQ i) (pQ j)))
    (z : AdjoinRoot ((f).map (algebraMap S Q))) (q : ι → S[X])
    (hz : ∀ i, component p i z =
      AdjoinRoot.mk (pQ i) ((cofactor p i * q i).map (algebraMap S Q))) :
    AdjoinRoot.mk ((f).map (algebraMap S Q))
      ((∑ i, cofactor p i*q i).map (algebraMap S Q)) = z := by
  apply components_injective p hcop
  funext i
  dsimp only
  rw [component_mk,Polynomial.map_sum,map_sum]
  rw [Finset.sum_eq_single i]
  · exact (hz i).symm
  · intro j _ hji
    apply AdjoinRoot.mk_eq_zero.mpr
    exact Polynomial.map_dvd (algebraMap S Q)
      (dvd_mul_of_dvd_left (cofactor_dvd_of_ne p hji) (q j))
  · intro hi
    exact (hi (Finset.mem_univ i)).elim
end Reconstruct
end PermanentBorder.FactorNormalization
namespace PermanentBorder.ReducedBranchConductor
open Polynomial FactorNormalization
section
variable {K S Q : Type*} [CommRing K] [CommRing S] [IsDomain S]
  [IsPrincipalIdealRing S] [IsLocalRing S] [IsAlgClosed (IsLocalRing.ResidueField S)]
  [Algebra K S] [CharP S 2]
  [Field Q] [Algebra S Q] [IsFractionRing S Q]

include K in

theorem reduced_local_realization (δ : Derivation K S S) (x : S) (hx : δ x=1)
    (f a b c d : S[X]) (hf : f.Monic)
    (hsep : (f.map (algebraMap S Q)).Separable)
    (hsq : f=a^2+C x*b^2+X*c^2+C x*X*d^2)
    (hder : f.derivative=c^2+C x*d^2)
    (z : S[X]) (hz : z ∈ enlargedGradientIdeal f b c d x)
    (t : AdjoinRoot (f.map (algebraMap S Q))) (ht : IsIntegral S t) :
    ∃ q : S[X], AdjoinRoot.mk (f.map (algebraMap S Q)) (q.map (algebraMap S Q)) =
      AdjoinRoot.mk (f.map (algebraMap S Q)) (z.map (algebraMap S Q))*t := by
  classical
  obtain ⟨s,p,hp,hprod⟩ := exists_factors hf hsep
  subst hprod
  have hfac (i : s) : (∏ j, p j) = p i * cofactor p i := (factor_mul_cofactor p i).symm
  have hcop : Pairwise (fun i j => IsCoprime
      ((p i).map (algebraMap S Q)) ((p j).map (algebraMap S Q))) := by
    intro i j hij
    have hh := hsep
    rw [hfac i,Polynomial.map_mul] at hh
    exact hh.isCoprime.of_isCoprime_of_dvd_right (Polynomial.map_dvd _ (cofactor_dvd_of_ne p hij))
  have ht' (i : s) : IsIntegral S (component (Q := Q) p i t) :=
    ht.map ((component (Q := Q) p i).restrictScalars S)
  have hr (i : s) := irreducible_realization δ x hx (∏j,p j) (p i) (cofactor p i)
    a b c d (hp i).1 (by rw [(hp i).2.1]; exact (hp i).2.2)
    (hfac i) hsep hsq hder z hz (component (Q := Q) p i t) (ht' i)
  choose q hq using hr
  refine ⟨∑ i, cofactor p i*q i,?_⟩
  apply reconstruct p hcop
  intro i
  rw [map_mul,component_mk]
  exact (hq i).symm
end
end PermanentBorder.ReducedBranchConductor
namespace PermanentBorder.ReducedBranchConductor
open Polynomial

section BaseChange
variable {S U : Type*} [CommRing S] [CommRing U] (ρ : S →+* U)

lemma gradient_map (f b c d : S[X]) (x : S) :
    Ideal.map (Polynomial.mapRingHom ρ) (gradientIdeal f b c d x) =
      gradientIdeal (f.map ρ) (b.map ρ) (c.map ρ) (d.map ρ) (ρ x) := by
  simp only [gradientIdeal,Ideal.map_span,Set.image_insert_eq,Set.image_singleton,
    coe_mapRingHom,Polynomial.map_add,Polynomial.map_pow,Polynomial.map_mul,Polynomial.map_X,Polynomial.map_C]

lemma enlarged_map_le (f b c d : S[X]) (x : S) :
    Ideal.map (Polynomial.mapRingHom ρ) (enlargedGradientIdeal f b c d x) ≤
      enlargedGradientIdeal (f.map ρ) (b.map ρ) (c.map ρ) (d.map ρ) (ρ x) := by
  rw [enlargedGradientIdeal,Ideal.map_sup,Ideal.map_mul,gradient_map]
  apply sup_le_sup le_rfl
  apply Ideal.mul_mono
  · simp only [Ideal.map_span,Set.image_singleton,coe_mapRingHom,Polynomial.map_pow]
    exact le_rfl
  · exact (Ideal.map_radical_le (Polynomial.mapRingHom ρ)).trans_eq (congrArg Ideal.radical (gradient_map ρ f b c d x))

end BaseChange

section LocalGlobal
variable {S Q : Type*} [CommRing S] [Field Q] [Algebra S Q]

lemma map_tower (U : Type*) [CommRing U] [Algebra S U] [Algebra U Q]
    [IsScalarTower S U Q] (f : S[X]) :
    f.map (algebraMap S Q) = (f.map (algebraMap S U)).map (algebraMap U Q) := by
  rw [map_map,← IsScalarTower.algebraMap_eq]

noncomputable def genericChange (U : Type*) [CommRing U] [Algebra S U] [Algebra U Q]
    [IsScalarTower S U Q] (f : S[X]) :
    AdjoinRoot (f.map (algebraMap S Q)) ≃ₐ[Q]
      AdjoinRoot ((f.map (algebraMap S U)).map (algebraMap U Q)) :=
  AdjoinRoot.algEquivOfEq Q _ _ (map_tower U f)

lemma genericChange_mk (U : Type*) [CommRing U] [Algebra S U] [Algebra U Q]
    [IsScalarTower S U Q] (f p : S[X]) :
    genericChange U f (AdjoinRoot.mk _ (p.map (algebraMap S Q))) =
      AdjoinRoot.mk _ ((p.map (algebraMap S U)).map (algebraMap U Q)) := by
  have he : (genericChange (Q := Q) U f).toAlgHom.comp
      (AdjoinRoot.mkₐ (f.map (algebraMap S Q))) =
      AdjoinRoot.mkₐ ((f.map (algebraMap S U)).map (algebraMap U Q)) := by
    ext
    exact AdjoinRoot.algEquivOfEq_root _ _ (map_tower U f)
  rw [← map_tower U p]
  exact AlgHom.congr_fun he _

end LocalGlobal

section Lattice
variable {S : Type*} [CommRing S] [IsDomain S]
local notation "Q" => FractionRing S

lemma polynomial_lattice_local_global (f : S[X])
    (t : AdjoinRoot (f.map (algebraMap S Q)))
    (hlocal : ∀ (P : Ideal S) [P.IsMaximal],
      ∃ q : (Localization.AtPrime P)[X],
        AdjoinRoot.mk _ (q.map (algebraMap (Localization.AtPrime P) Q)) =
          genericChange (Localization.AtPrime P) f t) :
    ∃ q : S[X], AdjoinRoot.mk _ (q.map (algebraMap S Q)) = t := by
  let E := AdjoinRoot (f.map (algebraMap S Q))
  let j : S[X] →ₐ[S] E := (AdjoinRoot.mkₐ _).restrictScalars S |>.comp
    (Polynomial.mapAlgHom (Algebra.ofId S Q))
  let N : Submodule S E := LinearMap.range j.toLinearMap
  let D : Ideal S := Submodule.comap (LinearMap.toSpanSingleton S E t) N
  have hD : D = ⊤ := by
    by_contra hn
    obtain ⟨P,hP,hDP⟩ := Ideal.exists_le_maximal D hn
    let := hP
    let U := Localization.AtPrime P
    obtain ⟨q,hq⟩ := hlocal P
    obtain ⟨s,hs,hsp⟩ := IsLocalization.integerNormalization_spec P.primeCompl q
    have hst : (s : S) • t ∈ N := by
      refine ⟨IsLocalization.integerNormalization P.primeCompl q,?_⟩
      change j _ = s • t
      apply (genericChange U f).injective
      change genericChange U f (AdjoinRoot.mk _ ((IsLocalization.integerNormalization P.primeCompl q).map (algebraMap S Q))) = _
      rw [genericChange_mk,hsp]
      change ((AdjoinRoot.mkₐ _).restrictScalars S)
        (((Polynomial.mapAlgHom (Algebra.ofId U Q)).restrictScalars S) (s • q)) =
        ((genericChange U f).restrictScalars S) (s • t)
      rw [map_smul,map_smul,map_smul]
      exact congrArg (fun u => s • u) hq

    have hsD : s ∈ D := hst
    exact hs (hDP hsD)
  have ht : t ∈ N := by
    have hh : (1:S) ∈ D := by rw [hD]; trivial
    simpa only [D,Submodule.mem_comap,LinearMap.toSpanSingleton_apply,one_smul] using hh
  exact ht
end Lattice

section Residue
variable {K : Type*} [Field K] [IsAlgClosed K]
lemma polynomial_residue_algClosed (P : Ideal K[X]) [P.IsMaximal] :
    IsAlgClosed P.ResidueField := by
  let : Algebra.FiniteType K P.ResidueField := Algebra.FiniteType.of_surjective
    (IsScalarTower.toAlgHom K K[X] P.ResidueField) P.algebraMap_residueField_surjective
  let : Module.Finite K P.ResidueField := finite_of_finite_type_of_isJacobsonRing K P.ResidueField
  exact IsAlgClosed.of_ringEquiv K _ (RingEquiv.ofBijective (algebraMap K P.ResidueField)
    IsAlgClosed.algebraMap_bijective_of_isIntegral)
end Residue
section Global
variable {K S : Type*} [CommRing K] [CommRing S] [IsDomain S]
  [IsPrincipalIdealRing S] [Algebra K S] [CharP S 2]
local notation "Q" => FractionRing S

theorem reduced_global_realization (δ : Derivation K S S) (x : S) (hx : δ x = 1)
    (hres : ∀ (P : Ideal S) [P.IsMaximal], IsAlgClosed P.ResidueField)
    (f a b c d : S[X]) (hf : f.Monic)
    (hsep : (f.map (algebraMap S Q)).Separable)
    (hsq : f=a^2+C x*b^2+X*c^2+C x*X*d^2)
    (hder : f.derivative=c^2+C x*d^2)
    (z : S[X]) (hz : z ∈ enlargedGradientIdeal f b c d x)
    (t : AdjoinRoot (f.map (algebraMap S Q))) (ht : IsIntegral S t) :
    ∃ q : S[X], AdjoinRoot.mk _ (q.map (algebraMap S Q)) =
      AdjoinRoot.mk _ (z.map (algebraMap S Q))*t := by
  apply polynomial_lattice_local_global
  intro P hP
  let U := Localization.AtPrime P
  let : IsAlgClosed (IsLocalRing.ResidueField U) := hres P
  let : CharP U 2 := charP_of_injective_algebraMap
    (IsLocalization.injective U P.primeCompl_le_nonZeroDivisors) 2
  let ρ := algebraMap S U
  let δ' := NormalizationDerivation.extendEtale (T := U) δ
  have hx' : δ' (ρ x) = 1 := by
    rw [NormalizationDerivation.extendEtale_algebraMap,hx,map_one]
  have ht' : IsIntegral U (genericChange U f t) :=
    (ht.map ((genericChange U f).restrictScalars S).toAlgHom).tower_top
  have hs' : (f.map ρ)= (a.map ρ)^2+C (ρ x)*(b.map ρ)^2+
      X*(c.map ρ)^2+C (ρ x)*X*(d.map ρ)^2 := by
    rw [hsq]
    simp only [Polynomial.map_add,Polynomial.map_pow,Polynomial.map_mul,
      Polynomial.map_C,Polynomial.map_X]
  have hd' : (f.map ρ).derivative = (c.map ρ)^2+C (ρ x)*(d.map ρ)^2 := by
    rw [Polynomial.derivative_map,hder]
    simp only [Polynomial.map_add,Polynomial.map_pow,Polynomial.map_mul,Polynomial.map_C]
  have hz' : z.map ρ ∈ enlargedGradientIdeal (f.map ρ) (b.map ρ) (c.map ρ) (d.map ρ) (ρ x) :=
    enlarged_map_le ρ f b c d x (Ideal.mem_map_of_mem (Polynomial.mapRingHom ρ) hz)
  obtain ⟨q,hq⟩ := reduced_local_realization δ' (ρ x) hx' (f.map ρ) (a.map ρ)
    (b.map ρ) (c.map ρ) (d.map ρ) (hf.map ρ) (by rw [← map_tower U f]; exact hsep)
    hs' hd' (z.map ρ) hz' (genericChange U f t) ht'
  refine ⟨q,?_⟩
  rw [map_mul,genericChange_mk]
  exact hq
end Global
end PermanentBorder.ReducedBranchConductor

end OAI
