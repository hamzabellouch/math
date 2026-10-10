import OAI.Geometry.LatticeCovering.PrimeKernels

namespace OAI

section
noncomputable section
noncomputable section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
section
noncomputable section
open Module Submodule MeasureTheory
open scoped BigOperators
noncomputable section
noncomputable section

namespace SingleLatticeCovering.PrimeKernel
open Set MeasureTheory Filter Topology AffineVoid ConvexGrid BrokenCircuit PrimeCircuit
open scoped Pointwise ENNReal BigOperators
variable {n : ℕ}

def liftCoeff {p : ℕ} (a : Fin n → ZMod p) : Fin (n+1) → ℤ :=
  Fin.cons 0 (fun j => (a j).val)

lemma modForm_liftCoeff (p : ℕ) (hp : 0<p) (a : Fin n → ZMod p) (z : Fin (n+1) → ℤ) :
    modForm p 0 (liftCoeff a) z = (z 0 : ZMod p)+
      ∑ j, (z j.succ : ZMod p)*a j := by
  let : NeZero p := ⟨hp.ne'⟩
  change (z 0 : ZMod p) +
    (∑ j ∈ Finset.univ.erase 0, (liftCoeff a j : ZMod p)*(z j : ZMod p)) = _
  congr 1
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ _)]
  simp [liftCoeff,Fin.sum_univ_succ,mul_comm]

def finResidue (p : ℕ) [NeZero p] : Fin p ≃ ZMod p where
  toFun b := (b.val:ZMod p)
  invFun b := ⟨b.val,ZMod.val_lt b⟩
  left_inv b := by apply Fin.ext; simp [ZMod.val_natCast,Nat.mod_eq_of_lt b.isLt]
  right_inv b := ZMod.natCast_zmod_val b

lemma card_badOffsets (p : ℕ) [Fact p.Prime] (a : Fin n → ZMod p)
    (S : Finset (Fin (n+1) → ℤ)) :
    ((badOffsets p 0 (liftCoeff a) S).card:ℝ) =
      ∑ b : ZMod p, normalizedMiss (fun z : S => fun j => (z.val j:ZMod p)) a b := by
  classical
  unfold badOffsets
  rw [←Finset.sum_boole]
  apply Fintype.sum_equiv (finResidue p)
  intro b
  unfold normalizedMiss
  congr 1
  apply propext
  simp only [finResidue,Equiv.coe_fn_mk,Subtype.forall,modForm_liftCoeff p (Nat.Prime.pos Fact.out),mul_comm]

abbrev ensembleFull (p : ℕ) (hp : 0<p) (a : Fin n → ZMod p) : Horizontal.FullLattice (n+1) :=
  normalizedFull p hp 0 (liftCoeff a)

def meanPrimeHole (J : Set (Fin (n+1) → ℝ)) (p : ℕ) [Fact p.Prime] : ℝ :=
  (∑ a : Fin n → ZMod p, ((ensembleFull p (Nat.Prime.pos Fact.out) a).hole J).toReal)/(p:ℝ)^n

lemma meanPrimeHole_le_grid (p : ℕ) [Fact p.Prime]
    (S : Finset (Fin (n+1) → ℤ)) {J : Set (Fin (n+1) → ℝ)} (hJ : IsCompact J)
    (hthick : ∀ z ∈ S, ∀ u ∈ gridUnitCell,
      gridMap p (Nat.Prime.pos Fact.out) z + normalizeEquiv p (Nat.Prime.pos Fact.out) u ∈ J) :
    meanPrimeHole J p ≤ meanNormalized (fun z : S => fun j => (z.val j:ZMod p)) := by
  classical
  have hp : 0<p := Nat.Prime.pos Fact.out
  have hpR : (0:ℝ)<p := by exact_mod_cast hp
  have hs : (∑ a : Fin n → ZMod p, ((ensembleFull p hp a).hole J).toReal) ≤
      ∑ a : Fin n → ZMod p, (∑ b : ZMod p,
        normalizedMiss (fun z : S => fun j => (z.val j:ZMod p)) a b)/(p:ℝ) := by
    apply Finset.sum_le_sum
    intro a ha
    have hh := ENNReal.toReal_mono
      (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by exact_mod_cast hp.ne'))
      (normalizedFull_hole_le_badOffsets p hp 0 (liftCoeff a) S hJ hthick)
    simpa only [ENNReal.toReal_div,ENNReal.toReal_natCast,card_badOffsets] using hh
  unfold meanPrimeHole meanNormalized
  simp only [ZMod.card]
  calc
    _ ≤ (∑ a : Fin n → ZMod p, (∑ b : ZMod p,
        normalizedMiss (fun z : S => fun j => (z.val j:ZMod p)) a b)/(p:ℝ))/(p:ℝ)^n :=
      div_le_div_of_nonneg_right hs (pow_nonneg hpR.le _)
    _ = _ := by rw [←Finset.sum_div,div_div,pow_succ]; congr 1; ring

lemma fintype_sum_irrel {A M : Type*} [AddCommMonoid M] (I₁ I₂ : Fintype A)
    (f g : A → M) (h : ∀ a, f a=g a) :
    @Finset.sum A M _ (@Finset.univ A I₁) f =
    @Finset.sum A M _ (@Finset.univ A I₂) g := by
  have he : I₁=I₂ := Subsingleton.elim _ _
  subst I₂
  exact @Fintype.sum_congr A M I₁ _ f g h

lemma fullMiss_eq_avoidance {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {σ : Type*} [Fintype σ] (v : σ → Fin (n+1) → K) (w : Fin (n+2) → K) :
    fullMiss v w=avoidanceIndicator (fun z => Fin.cons 1 (v z)) (dotProductBilin K K w) := by
  classical
  have he (i : σ) : (∑ j, w j * (Fin.cons (1:K) (v i) : Fin (n+2) → K) j) =
      (dotProductBilin K K w) (Fin.cons 1 (v i)) := by
    change (∑ j : Fin (n+2), w j * (Fin.cons (1:K) (v i) : Fin (n+2) → K) j) =
      ∑ j : Fin (n+2), w j * (Fin.cons (1:K) (v i) : Fin (n+2) → K) j
    exact fintype_sum_irrel _ _ _ _ (fun j => rfl)
  unfold fullMiss avoidanceIndicator
  split_ifs with h₁ h₂ h₂
  · rfl
  · exfalso
    apply h₂
    intro i
    exact (he i).symm ▸ h₁ i
  · exfalso
    apply h₁
    intro i
    exact (he i) ▸ h₂ i
  · rfl

lemma meanFull_generic {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {σ : Type*} [Fintype σ] (v : σ → Fin (n+1) → K) :
    meanFull v=vectorAverage (fun w : Fin (n+2) → K =>
      avoidanceIndicator (fun z => Fin.cons 1 (v z)) (dotProductBilin K K w)) := by
  classical
  unfold meanFull vectorAverage
  simp only [Fintype.card_fun,Fintype.card_fin,Nat.cast_pow]
  apply congrArg (fun t : ℝ => t/(Fintype.card K:ℝ)^(n+2))
  exact fintype_sum_irrel _ _ _ _ (fullMiss_eq_avoidance v)

lemma meanFull_integerGrid {J : Set (Fin (n+1) → ℝ)} (hJ : IsCompact J)
    (p : ℕ) [Fact p.Prime] :
    meanFull (fun z : integerGrid J hJ (primeScale (n+1) p) =>
      fun j => (z.val j:ZMod p))=primeGridVoid J hJ p := by
  exact meanFull_generic _

lemma scaleFactor_eq_primeScale_inv (d p : ℕ) :
    scaleFactor (ι:=Fin d) p=(primeScale d p)⁻¹ := by
  simp only [scaleFactor,Fintype.card_fin,primeScale]
  exact Real.rpow_neg (Nat.cast_nonneg _) _

lemma gridMap_eq_scaledIntegerPoint (d p : ℕ) (hp : 0<p) (z : Fin d → ℤ) :
    gridMap p hp z=scaledIntegerPoint (primeScale d p) z := by
  ext j
  change scaleFactor (ι:=Fin d) p*(z j:ℝ)=_
  rw [scaleFactor_eq_primeScale_inv]
  rfl

lemma gridUnitCell_norm_le {d : ℕ} {u : Fin d → ℝ} (hu : u ∈ gridUnitCell) : ‖u‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
  intro j
  have hh := (Set.mem_pi.mp hu) j (Set.mem_univ _)
  simpa only [Real.norm_eq_abs,abs_of_nonneg hh.1] using hh.2.le

lemma eventually_grid_thick {d : ℕ} (hd : 0<d) {J C : Set (Fin d → ℝ)}
    (hC : IsCompact C) (hsub : C ⊆ interior J) :
    ∀ᶠ p : ℕ in atTop, ∀ hp : 0<p,
      ∀ z ∈ integerGrid C hC (primeScale d p), ∀ u ∈ gridUnitCell,
        gridMap p hp z + normalizeEquiv p hp u ∈ J := by
  obtain ⟨δ,hδ,hs⟩ := ConvexCore.compact_uniform_add hC hsub
  have ht : Tendsto (fun p => (primeScale d p)⁻¹) atTop (𝓝 (0:ℝ)) :=
    tendsto_inv_atTop_zero.comp (primeScale_tendsto hd)
  filter_upwards [ht.eventually (gt_mem_nhds hδ)] with p hpδ hp z hz u hu
  apply hs (gridMap p hp z)
  · rw [gridMap_eq_scaledIntegerPoint]
    exact (mem_integerGrid hC (primeScale_pos hp).ne').mp hz
  · change ‖scaleFactor (ι:=Fin d) p • u‖ ≤ δ
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (scaleFactor_pos p hp)]
    calc
      _ ≤ scaleFactor (ι:=Fin d) p * 1 :=
        mul_le_mul_of_nonneg_left (gridUnitCell_norm_le hu) (scaleFactor_pos p hp).le
      _ ≤ δ := by rw [mul_one,scaleFactor_eq_primeScale_inv]; exact hpδ.le



end SingleLatticeCovering.PrimeKernel

namespace SingleLatticeCovering.AffineVoid
open Filter Topology
lemma conditioning_factor_tendsto :
    Tendsto (fun p : ℕ => (p:ℝ)/((p:ℝ)-1)) atTop (𝓝 (1:ℝ)) := by
  have hden : Tendsto (fun p : ℕ => (p:ℝ)-1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [(tendsto_natCast_atTop_atTop : Tendsto (fun p : ℕ => (p:ℝ)) atTop atTop).eventually
      (eventually_ge_atTop (b+1))] with p hp
    linarith
  have ht : Tendsto (fun p : ℕ => 1+((p:ℝ)-1)⁻¹) atTop (𝓝 (1:ℝ)) := by
    simpa only [Function.comp_def,add_zero] using
      (tendsto_inv_atTop_zero.comp hden).const_add 1
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 2] with p hp
  have hpR : (2:ℝ) ≤ p := by exact_mod_cast hp
  have hn : (p:ℝ)-1 ≠ 0 := by linarith
  field_simp [hn]
  ring

lemma eventually_factor_mul_lt {A B : ℝ} (hAB : A<B) :
    ∀ᶠ p : ℕ in atTop, ((p:ℝ)/((p:ℝ)-1))*A < B := by
  have ht := conditioning_factor_tendsto.mul_const A
  rw [one_mul] at ht
  exact ht.eventually (gt_mem_nhds hAB)
end SingleLatticeCovering.AffineVoid

namespace SingleLatticeCovering.PrimeKernel
open Set MeasureTheory Filter Topology AffineVoid ConvexGrid RogersPreparation ConvexCore SimplexYoung
open scoped Pointwise ENNReal BigOperators
variable {n : ℕ}



theorem eventually_meanPrimeHole_centered_source (hd : 270 ≤ n+1)
    {J : Set (Fin (n+1) → ℝ)} (hJ : IsCompact J) (hconv : Convex ℝ J)
    (h0 : 0 ∈ interior J) (hV : 0 < volume.real J)
    (hVeta : volume.real J ≤ sourceEta (n+1)) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (p : ℕ) [Fact p.Prime], N ≤ p →
      meanPrimeHole J p ≤ Real.exp (-volume.real J)+300*Real.exp (-sourceEta (n+1))+ε := by
  obtain ⟨c,hc0,hc1,hcexp⟩ := exists_shrink_exp (d:=n+1) (V:=volume.real J)
    (show 0<ε/3 by linarith)
  let C := c • J
  have hC : IsCompact C := core_compact hJ c
  have hCconv : Convex ℝ C := hconv.smul c
  have hCsub : C ⊆ interior J := core_subset_interior hconv h0 hc0.le hc1
  have hC0 : 0 ∈ C := ⟨0,interior_subset h0,smul_zero c⟩
  have hCV : volume.real C=c^(n+1)*volume.real J := core_volume hc0.le
  have hCVpos : 0<volume.real C := by rw [hCV]; positivity
  have hCVeta : volume.real C≤ sourceEta (n+1) := by
    rw [hCV]
    exact (mul_le_of_le_one_left hV.le (pow_le_one₀ hc0.le hc1.le)).trans hVeta
  obtain ⟨N₁,hN₁⟩ := eventually_primeGridVoid_source hd hC hCconv hC0 hCVpos hCVeta
    (show 0<ε/3 by linarith)
  obtain ⟨N₂,hN₂⟩ := eventually_atTop.mp (eventually_grid_thick (Nat.succ_pos n) hC hCsub)
  obtain ⟨N₃,hN₃⟩ := eventually_atTop.mp (eventually_factor_mul_lt
    (A:=Real.exp (-volume.real J)+300*Real.exp (-sourceEta (n+1))+2*ε/3)
    (B:=Real.exp (-volume.real J)+300*Real.exp (-sourceEta (n+1))+ε)
    (by linarith))
  refine ⟨max N₁ (max N₂ N₃),fun p hp hpN => ?_⟩
  have hp0 : 0<p := Nat.Prime.pos Fact.out
  have hp1 : (1:ℝ)<p := by exact_mod_cast Nat.Prime.one_lt (Fact.out : Nat.Prime p)
  have hpR : (0:ℝ)<p := by linarith
  have hM := meanPrimeHole_le_grid p (integerGrid C hC (primeScale (n+1) p)) hJ
    (hN₂ p ((le_max_left N₂ N₃).trans ((le_max_right N₁ (max N₂ N₃)).trans hpN)) hp0)
  have hcond := conditioning_bound (fun z : integerGrid C hC (primeScale (n+1) p) =>
    fun j => (z.val j:ZMod p))
  rw [ZMod.card,meanFull_integerGrid] at hcond
  have hh := hN₁ p ((le_max_left _ _).trans hpN)
  have hsmall : primeGridVoid C hC p ≤
      Real.exp (-volume.real J)+300*Real.exp (-sourceEta (n+1))+2*ε/3 := by
    rw [←hCV] at hcexp
    linarith
  exact hM.trans (hcond.trans ((mul_le_mul_of_nonneg_left hsmall
    (div_nonneg hpR.le (by linarith))).trans
    (hN₃ p ((le_max_right N₂ N₃).trans ((le_max_right N₁ (max N₂ N₃)).trans hpN))).le))


end SingleLatticeCovering.PrimeKernel

namespace SingleLatticeCovering.Horizontal
open Set MeasureTheory Completion
open scoped Pointwise
lemma FullLattice.hole_vadd {d : ℕ} (L : FullLattice d)
    (v : Fin d → ℝ) (J : Set (Fin d → ℝ)) : L.hole (v+ᵥJ)=L.hole J := by
  have he : latticeProjection L.module '' (v+ᵥJ)=
      latticeProjection L.module v +ᵥ (latticeProjection L.module '' J) := by
    ext y
    constructor
    · rintro ⟨_,⟨x,hx,rfl⟩,rfl⟩
      exact ⟨latticeProjection L.module x,⟨x,hx,rfl⟩,(map_add _ _ _).symm⟩
    · rintro ⟨_,⟨x,hx,rfl⟩,rfl⟩
      exact ⟨v+x,⟨x,hx,rfl⟩,map_add _ _ _⟩
  unfold FullLattice.hole
  rw [he,←vadd_set_compl,measure_vadd]
end SingleLatticeCovering.Horizontal

namespace SingleLatticeCovering.PrimeKernel
open Set MeasureTheory Filter Topology AffineVoid ConvexGrid RogersPreparation ConvexCore SimplexYoung
open scoped Pointwise ENNReal BigOperators
variable {n : ℕ}

lemma meanPrimeHole_vadd (v : Fin (n+1) → ℝ) (J : Set (Fin (n+1) → ℝ))
    (p : ℕ) [Fact p.Prime] : meanPrimeHole (v+ᵥJ) p=meanPrimeHole J p := by
  classical
  unfold meanPrimeHole
  simp only [Horizontal.FullLattice.hole_vadd]



theorem eventually_meanPrimeHole_source (hd : 270 ≤ n+1)
    {J : Set (Fin (n+1) → ℝ)} (hJ : IsCompact J) (hconv : Convex ℝ J)
    (hV : 0 < volume.real J) (hVeta : volume.real J ≤ sourceEta (n+1))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (p : ℕ) [Fact p.Prime], N ≤ p →
      meanPrimeHole J p ≤ Real.exp (-volume.real J)+300*Real.exp (-sourceEta (n+1))+ε := by
  obtain ⟨v,hv⟩ := interior_nonempty_of_volume_pos hconv hV
  let C := (-v)+ᵥJ
  have hC : IsCompact C := IsCompact.vadd (-v) hJ
  have hCconv : Convex ℝ C := hconv.vadd (-v)
  have hC0 : 0 ∈ interior C := by
    rw [show interior C=(-v)+ᵥinterior J from interior_vadd (-v) J]
    exact ⟨v,hv,neg_add_cancel v⟩
  have hCV : volume.real C=volume.real J := by
    unfold Measure.real
    rw [measure_vadd]
  obtain ⟨N,hN⟩ := eventually_meanPrimeHole_centered_source hd hC hCconv hC0
    (by rwa [hCV]) (by rwa [hCV]) hε
  refine ⟨N,fun p hp hpN => ?_⟩
  have hh := hN p hpN
  rw [hCV] at hh
  simpa only [C,meanPrimeHole_vadd] using hh


end SingleLatticeCovering.PrimeKernel

namespace SingleLatticeCovering.PrimeKernel
open Set MeasureTheory Filter Topology Horizontal ConvexGrid SimplexYoung
open scoped Pointwise ENNReal BigOperators
variable {n : ℕ}

lemma ensembleFull_covolume (p : ℕ) (hp : 0 < p) (a : Fin n → ZMod p) :
    ZLattice.covolume (ensembleFull p hp a).module=1 :=
  covolume_normalized p hp 0 (liftCoeff a)

lemma meanPrimeHole_le_one (J : Set (Fin (n+1) → ℝ)) (p : ℕ) [Fact p.Prime] :
    meanPrimeHole J p ≤ 1 := by
  classical
  have hp : 0 < p := Nat.Prime.pos Fact.out
  have hpR : (0:ℝ) < p := by exact_mod_cast hp
  unfold meanPrimeHole
  apply (div_le_one (pow_pos hpR n)).mpr
  calc
    _ ≤ ∑ _a : Fin n → ZMod p, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro a ha
      have hh : (ensembleFull p hp a).hole J ≤ 1 := by
        unfold FullLattice.hole
        exact prob_le_one
      simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono ENNReal.one_ne_top hh
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fun,
      Fintype.card_fin,ZMod.card,nsmul_eq_mul,Nat.cast_pow,mul_one]


theorem eventually_meanPrimeHole_all (hd : 270 ≤ n+1)
    {J : Set (Fin (n+1) → ℝ)} (hJ : IsCompact J) (hconv : Convex ℝ J)
    (hVeta : volume.real J ≤ sourceEta (n+1)) :
    ∃ N : ℕ, ∀ (p : ℕ) [Fact p.Prime], N ≤ p →
      meanPrimeHole J p ≤ Real.exp (-volume.real J)+301*Real.exp (-sourceEta (n+1)) := by
  by_cases hV : 0<volume.real J
  · obtain ⟨N,hN⟩ := eventually_meanPrimeHole_source hd hJ hconv hV hVeta
      (Real.exp_pos (-sourceEta (n+1)))
    refine ⟨N,fun p hp hpN => ?_⟩
    linarith [hN p hpN]
  · have hV0 : volume.real J=0 := le_antisymm (not_lt.mp hV) measureReal_nonneg
    refine ⟨0,fun p hp hpN => ?_⟩
    rw [hV0,neg_zero,Real.exp_zero]
    have hh := meanPrimeHole_le_one J p
    linarith [Real.exp_pos (-sourceEta (n+1))]


end SingleLatticeCovering.PrimeKernel

namespace SingleLatticeCovering.PrimeKernel
open Set MeasureTheory Filter Topology Horizontal ConvexGrid SimplexYoung
open scoped Pointwise ENNReal BigOperators
variable {n : ℕ}

lemma exists_le_finite_average {A : Type*} [Fintype A] [Nonempty A] (f : A → ℝ) :
    ∃ a, f a ≤ (Fintype.card A : ℝ)⁻¹*∑ b, f b := by
  have hc : (Fintype.card A : ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  have he : (∑ a : A, f a)=∑ _a : A, (Fintype.card A : ℝ)⁻¹*∑ b, f b := by
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    rw [←mul_assoc,mul_inv_cancel₀ hc,one_mul]
  obtain ⟨a,_,ha⟩ := Finset.exists_le_of_sum_le (Finset.univ_nonempty (α := A)) he.le
  exact ⟨a,ha⟩

lemma weighted_meanPrimeHole_sample {I : Type*} [Fintype I]
    (p : ℕ) [Fact p.Prime] (J : I → Set (Fin (n+1) → ℝ)) (w : I → ℝ) :
    ∃ a : Fin n → ZMod p,
      (∑ i, w i*((ensembleFull p (Nat.Prime.pos Fact.out) a).hole (J i)).toReal) ≤
        ∑ i, w i*meanPrimeHole (J i) p := by
  classical
  obtain ⟨a,ha⟩ := exists_le_finite_average
    (fun a : Fin n → ZMod p => ∑ i, w i*((ensembleFull p (Nat.Prime.pos Fact.out) a).hole (J i)).toReal)
  refine ⟨a,ha.trans_eq ?_⟩
  rw [Fintype.card_fun,Fintype.card_fin,ZMod.card,Nat.cast_pow,Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  unfold meanPrimeHole
  rw [←Finset.mul_sum]
  ring



theorem common_horizontal_source {I : Type*} [Fintype I]
    (J : I → Set (Fin (n+1) → ℝ)) (hJ : ∀ i, IsCompact (J i))
    (hconv : ∀ i, Convex ℝ (J i)) (hd : 270 ≤ n+1)
    (hVeta : ∀ i, volume.real (J i) ≤ sourceEta (n+1))
    (hcrit : 302*(∑ i, Real.exp (-volume.real (J i)/2)) ≤ 1) :
    ∃ L : FullLattice (n+1), ZLattice.covolume L.module=1 ∧ ∀ i,
      L.hole (J i) ≤ ENNReal.ofReal (Real.exp (-volume.real (J i)/2)) := by
  classical
  choose N hN using fun i => eventually_meanPrimeHole_all hd (hJ i) (hconv i) (hVeta i)
  obtain ⟨p,hpN,hpPrime⟩ := Nat.exists_infinite_primes (Finset.univ.sup N)
  let : Fact p.Prime := ⟨hpPrime⟩
  have hp : 0 < p := hpPrime.pos
  obtain ⟨a,ha⟩ := weighted_meanPrimeHole_sample p J
    (fun i => Real.exp (volume.real (J i)/2))
  have hnumeric (i : I) : Real.exp (volume.real (J i)/2)*meanPrimeHole (J i) p ≤
      302*Real.exp (-volume.real (J i)/2) := by
    have hh := mul_le_mul_of_nonneg_left
      (hN i p ((Finset.le_sup (f:=N) (Finset.mem_univ i)).trans hpN))
      (Real.exp_pos (volume.real (J i)/2)).le
    have hfirst : Real.exp (volume.real (J i)/2)*Real.exp (-volume.real (J i)) =
        Real.exp (-volume.real (J i)/2) := by rw [←Real.exp_add]; congr 1; ring
    have hsecond : Real.exp (volume.real (J i)/2)*Real.exp (-sourceEta (n+1)) ≤
        Real.exp (-volume.real (J i)/2) := by
      rw [←Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith [hVeta i])
    calc
      _ ≤ Real.exp (volume.real (J i)/2) *
          (Real.exp (-volume.real (J i))+301*Real.exp (-sourceEta (n+1))) := hh
      _ = Real.exp (-volume.real (J i)/2)+
          301*(Real.exp (volume.real (J i)/2)*Real.exp (-sourceEta (n+1))) := by
        rw [mul_add,hfirst]
        ring
      _ ≤ Real.exp (-volume.real (J i)/2)+301*Real.exp (-volume.real (J i)/2) :=
        add_le_add_right (mul_le_mul_of_nonneg_left hsecond (by norm_num : (0:ℝ) ≤ 301)) _
      _ = _ := by ring
  have hsum : (∑ i, Real.exp (volume.real (J i)/2)*((ensembleFull p hp a).hole (J i)).toReal) ≤ 1 := by
    apply ha.trans
    have hs := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hnumeric i)
    rw [←Finset.mul_sum] at hs
    exact hs.trans hcrit
  refine ⟨ensembleFull p hp a,ensembleFull_covolume p hp a,fun i => ?_⟩
  have hsingle := Finset.single_le_sum (s:=Finset.univ)
    (f:=fun j => Real.exp (volume.real (J j)/2)*((ensembleFull p hp a).hole (J j)).toReal)
    (fun j _ => mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg) (Finset.mem_univ i)
  have hh := mul_le_mul_of_nonneg_left (hsingle.trans hsum)
    (Real.exp_pos (-volume.real (J i)/2)).le
  have he : Real.exp (-volume.real (J i)/2)*Real.exp (volume.real (J i)/2)=1 := by
    rw [←Real.exp_add]
    rw [show -volume.real (J i)/2+volume.real (J i)/2=0 by ring,Real.exp_zero]
  simp only [←mul_assoc,he,one_mul,mul_one] at hh
  have hf : (ensembleFull p hp a).hole (J i)≠∞ := by
    unfold FullLattice.hole
    exact measure_ne_top _ _
  exact (ENNReal.toReal_le_toReal hf ENNReal.ofReal_ne_top).mp
    (by rw [ENNReal.toReal_ofReal (Real.exp_pos _).le]; exact hh)


end SingleLatticeCovering.PrimeKernel


namespace SingleLatticeCovering.PrimeKernel
open SimplexYoung Inputs Horizontal MeasureTheory Set
open scoped ENNReal BigOperators
variable {n : ℕ}




theorem scaled_common_horizontal_source {I : Type*} [Fintype I]
    (J : I → Set (Fin (n+1) → ℝ)) (hJ : ∀ i, IsCompact (J i))
    (hconv : ∀ i, Convex ℝ (J i)) (hd : 270 ≤ n+1) (Dh : ℝ) (hDh : 0 < Dh)
    (hu : ∀ i, (volume (J i)).toReal/Dh ≤ sourceEta (n+1))
    (hcrit : 302*(∑ i, Real.exp (-((volume (J i)).toReal/Dh)/2)) ≤ 1) :
    ∃ L : FullLattice (n+1), ZLattice.covolume L.module=Dh ∧ ∀ i,
      L.hole (J i) ≤ ENNReal.ofReal (Real.exp (-((volume (J i)).toReal/Dh)/2)) := by
  let e := determinantScale (n+1) Dh hDh
  have hdet : |LinearMap.det e.toLinearMap|=Dh := by
    rw [determinantScale_det (Nat.succ_pos n),abs_of_pos hDh]
  let J' : I → Set (Fin (n+1) → ℝ) := fun i => e.symm '' J i
  have hc (i : I) : IsCompact (J' i) := compact_linear_preimage (hJ i) e
  have hv (i : I) : volume.real (J' i)=(volume (J i)).toReal/Dh :=
    determinant_preimage_volume e Dh hDh hdet (J i)
  obtain ⟨L,hLc,hL⟩ := common_horizontal_source J' hc
    (fun i => (hconv i).linear_image e.symm.toLinearMap) hd
    (by intro i; rw [hv i]; exact hu i) (by simpa only [hv] using hcrit)
  refine ⟨L.image e,?_,?_⟩
  · rw [FullLattice.image_covolume,hdet,hLc,mul_one]
  · intro i
    have hh := L.image_hole e (hc i)
    have he : e '' J' i=J i := e.image_symm_image (J i)
    rw [he] at hh
    rw [hh]
    simpa only [hv] using hL i



theorem common_horizontal_from_circuits {m : ℕ} {α : Type*}
    (J : α → Set (Fin m → ℝ)) (s : Finset α) (Dh τ N : ℝ)
    (hm : 270 ≤ m) (hDh : 0 < Dh)
    (hJ : ∀ a∈s, IsCompact (J a)) (hconv : ∀ a∈s, Convex ℝ (J a))
    (hlo : ∀ a∈s, τ ≤ (volume (J a)).toReal/Dh)
    (hhi : ∀ a∈s, (volume (J a)).toReal/Dh ≤ sourceEta m)
    (hcard : (s.card : ℝ) ≤ N)
    (hcriterion : 302*N*Real.exp (-τ/2)<1) :
    ∃ L : FullLattice m, ZLattice.covolume L.module=Dh ∧ ∀ a∈s,
      L.hole (J a) ≤ ENNReal.ofReal (Real.exp (-((volume (J a)).toReal/Dh)/2)) := by
  classical
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m≠0)
  let I := {a // a∈s}
  have hsum : 302*(∑ i : I, Real.exp (-((volume (J i.val)).toReal/Dh)/2)) ≤ 1 := by
    calc
      _ ≤ 302*(∑ _i : I, Real.exp (-τ/2)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 302)
        exact Finset.sum_le_sum (fun i _ => Real.exp_le_exp.mpr (by linarith [hlo i.val i.prop]))
      _ = 302*(s.card : ℝ)*Real.exp (-τ/2) := by
        simp only [Finset.sum_const,Finset.card_univ,I,Fintype.card_coe,nsmul_eq_mul]
        ring
      _ ≤ 302*N*Real.exp (-τ/2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcard (by norm_num)) (Real.exp_pos _).le
      _ ≤ 1 := hcriterion.le
  obtain ⟨L,hLc,hL⟩ := scaled_common_horizontal_source (fun i : I => J i.val)
    (fun i => hJ i.val i.prop) (fun i => hconv i.val i.prop) hm Dh hDh
    (fun i => hhi i.val i.prop) hsum
  exact ⟨L,hLc,fun a ha => hL ⟨a,ha⟩⟩



end SingleLatticeCovering.PrimeKernel


noncomputable section
namespace SingleLatticeCovering.Assembly
open PrimeKernel SimplexYoung MeasureTheory Folded LatticeGeometry Completion Shear CoverGeometry Vertical Sections Horizontal
open scoped BigOperators Pointwise ENNReal




theorem sections_and_circuits_cover {B : Block} (c : Chain B) {m : ℕ}
    (hm : 270 ≤ m) (hD : 0 < c.fullDim)
    (K : Set (Fin (m+c.fullDim) → ℝ)) (hK : IsCompact K) (hconv : Convex ℝ K)
    (hV : 0 < (volume K).toReal) {R : ℝ} (hR : 0 < R)
    (hrad : c.radiusSq+(B.terminalDim : ℝ) ≤ R^2)
    (hsmall : R^2/(m : ℝ)^2 ≤ 1)
    (hgauss : ∀ y : c.FullVec, ‖WithLp.toLp 2 y‖ ≤ 6*(c.fullDim : ℝ)*R →
      (volume K).toReal*gamma y/2 ≤ (volume (coordinateFiber K y)).toReal)
    (κ ρ ε τ A : ℝ) (hρ : 0 < ρ) (hτ : 0 ≤ τ) (hA : 0 < A)
    (hpat : ∀ y : c.FullVec, ∃ P : Finset c.FullVec,
      P.Nonempty ∧ SuffixBinary P ∧
      (∀ l ∈ P, l ∈ c.fullRaw ∧ c.FullResidual y l ∧ c.det*gamma (y-c.fullLinear l) ≤ ε) ∧
      κ ≤ ∑ l ∈ P, c.det*gamma (y-c.fullLinear l))
    (hload : A+(2^c.fullDim : ℕ)*τ ≤ (Real.exp (-1)/8)*κ*ρ)
    (hcap : (Real.exp 1/8)*ρ*ε ≤ FinalRates.eta m)
    (hcriterion : 302*(3*(m : ℝ)^2)^c.fullDim*Real.exp (-τ/2)<1)
    (hcount : ∀ {α : Type} (s : Finset α), (s.card : ℝ) ≤ (3*(m : ℝ)^2)^c.fullDim →
      let Lstar := 2*((patternTotal c.alphabetSeq s c.fullDim : ℝ)+1)
      1 ≤ Lstar ∧ (patternTotal c.alphabetSeq s c.fullDim : ℝ)<Lstar ∧
      Real.exp ((2 : ℝ)^c.fullDim*Real.log Lstar-A/2) ≤
        1/((m+c.fullDim : ℕ) : ℝ)^(2*(m+c.fullDim))) :
    ∃ (Λ : Submodule ℤ (Fin (m+c.fullDim) → ℝ)) (_ : DiscreteTopology Λ),
      IsZLattice ℝ Λ ∧ K+(Λ : Set (Fin (m+c.fullDim) → ℝ))=Set.univ ∧
      (volume K).toReal/ZLattice.covolume Λ volume ≤ Real.exp 1*ρ := by
  classical
  let Dh := (volume K).toReal/(ρ*c.det)
  have hDh : 0 < Dh := div_pos hV (mul_pos hρ c.det_pos)
  obtain ⟨e,heK,heconv,hevol,S,hSc,J,hJ,hsections⟩ :=
    coordinate_marginal_to_labels (by omega : 2 ≤ m) hD hK hconv hV hR hsmall hgauss
  let α := {a // a ∈ S}
  let J' : α → Set (Fin m → ℝ) := fun a => J a.val
  let u : α → ℝ := fun a => (volume (J' a)).toReal/Dh
  let s : Finset α := Finset.univ.filter (fun a => τ ≤ u a ∧ u a ≤ (Real.exp 1/8)*ρ*ε)
  have hcard : (s.card : ℝ) ≤ (3*(m : ℝ)^2)^c.fullDim := by
    have hh : s.card ≤ S.card := by
      calc
        s.card ≤ (Finset.univ : Finset α).card := Finset.card_le_card (Finset.filter_subset _ _)
        _ = S.card := by simp [α]
    exact (by exact_mod_cast hh : (s.card : ℝ) ≤ S.card).trans hSc
  have hulo (a : α) (ha : a ∈ s) : τ ≤ u a := (Finset.mem_filter.mp ha).2.1
  have huhi (a : α) (ha : a ∈ s) : u a ≤ FinalRates.eta m :=
    ((Finset.mem_filter.mp ha).2.2).trans hcap
  obtain ⟨L,hLc,hLhole⟩ := common_horizontal_from_circuits J' s Dh
    τ ((3*(m : ℝ)^2)^c.fullDim) hm hDh
    (by intro a ha; exact (hJ a.val a.property).1)
    (by intro a ha; exact (hJ a.val a.property).2.1)
    hulo huhi hcard hcriterion
  let Lstar := 2*((patternTotal c.alphabetSeq s c.fullDim : ℝ)+1)
  obtain ⟨hLstar,hcost,herror⟩ := hcount s hcard
  have hV' : 0 < (volume (e '' K)).toReal := by rwa [hevol]
  have hcov' : ZLattice.covolume L.module volume=(volume (e '' K)).toReal/(ρ*c.det) := by
    rw [hevol]; exact hLc
  obtain ⟨Λ,hd,hfull,hcover,hbound⟩ := labeled_chain_to_cover c (by omega) L.module (e '' K)
    heK heconv hV' J' (fun a => (hJ a.val a.property).1)
    κ ρ (Real.exp (-1)/8) (Real.exp 1/8) ε τ A Lstar hρ (by positivity) (by positivity)
    hτ hA hcov' hpat (by
      intro v hv
      obtain ⟨a,ha,hin,hl,hu⟩ := hsections v (hv.trans hrad)
      exact ⟨⟨a,ha⟩,hin,hl,hu⟩) (by
      intro a hlo hhi
      have ha : a ∈ s := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _,?_,?_⟩
        · simpa only [hLc] using hlo
        · simpa only [hLc] using hhi
      simpa only [FullLattice.hole,hLc] using hLhole a ha) hload hLstar (by
      simpa only [hLc,s,u,patternTotal,Lstar] using hcost) (by
      simpa only [Nat.cast_pow,Nat.cast_ofNat] using herror)
  let := hd
  let := hfull
  exact pull_back_cover e K Λ hcover hbound


end SingleLatticeCovering.Assembly


noncomputable section
namespace SingleLatticeCovering.Assembly
open PrimeKernel SimplexYoung MeasureTheory Folded LatticeGeometry Completion Shear CoverGeometry Vertical Sections Horizontal Inputs
open Filter Topology
open scoped BigOperators Pointwise ENNReal




theorem eventual_main_reduction_circuits {α β γ C₀ : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hC₀ : 0 ≤ C₀)
    (hGaussian : ∀ᶠ n : ℕ in atTop, GaussianPositions α β γ C₀ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ K : Set (Fin n → ℝ),
      IsCompact K → Convex ℝ K → (interior K).Nonempty →
      ∃ (Λ : Submodule ℤ (Fin n → ℝ)) (_ : DiscreteTopology Λ), IsZLattice ℝ Λ ∧
        K+(Λ : Set (Fin n → ℝ))=Set.univ ∧
        (volume K).toReal/ZLattice.covolume Λ volume ≤ C*(n : ℝ)*Real.log (n : ℝ) := by
  classical
  obtain ⟨cutoff,hcut,C,k,κ,hC,hk,hκ,hvertical⟩ := vertical_patterns_alphabets
  let CT : ℝ := 301
  have hCT : 0 ≤ CT := by norm_num [CT]
  have hCTeq : 1+CT=302 := by norm_num [CT]
  obtain ⟨Cstar,hstar,hconditions⟩ := FinalRates.final_conditions hC hk
    (show 0 < Real.exp (-1)/8 by positivity) (show 0 ≤ Real.exp 1/8 by positivity)
    hκ (show (1 : ℝ) ≤ 3 by norm_num) hCT
  refine ⟨Real.exp 1*Cstar,by positivity,?_⟩
  filter_upwards [hconditions,FinalRates.eventually_marginal_scales hC hα hβ hγ hC₀,
    FinalRates.firstSize_tendsto.eventually (eventually_ge_atTop cutoff), hGaussian,
      FinalRates.eventually_dimension_small hC,eventually_ge_atTop (540 : ℕ)]
      with n hn hscale hfirst hgaussian hdim hn540
  obtain ⟨B,c,hcb,hcs,hDim,hRad,hAlphabet,hPattern⟩ := hvertical (FinalRates.firstSize n) hfirst
  have hDdim : (c.fullDim : ℝ) ≤ C*((FinalRates.firstSize n : ℝ)+1) := by
    simpa [Chain.fullDim,Nat.cast_add] using hDim
  obtain ⟨hDn,hm,hcap,hload,hcrit,hcount⟩ := hn.2 c.fullDim hDdim
  have hm270 : 270 ≤ n-c.fullDim := by
    have hd := (hdim c.fullDim hDdim).2
    have hnR : (540 : ℝ) ≤ n := by exact_mod_cast hn540
    have hh : (270 : ℝ) ≤ ((n-c.fullDim : ℕ) : ℝ) := by
      rw [Nat.cast_sub hDn]
      linarith
    exact_mod_cast hh
  rw [hCTeq] at hcrit
  obtain ⟨_,_,hDpower,hRadius,hErr,hSmall⟩ := hscale c.fullDim hDdim
  have hD : 0 < c.fullDim := by
    have hfirstdim := chain_first_le_dim c
    rw [hcb] at hfirstdim
    dsimp [Chain.fullDim]
    omega
  let m := n-c.fullDim
  have hmn : m+c.fullDim=n := Nat.sub_add_cancel hDn
  have hmnle : m ≤ n := Nat.sub_le _ _
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  let ρ := Cstar*(n : ℝ)*Real.log (n : ℝ)
  let ε := Real.exp (-k*(FinalRates.firstSize n : ℝ)^(70/100 : ℝ))
  let R := FinalRates.sectionRadius C n
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hrad : c.radiusSq+(B.terminalDim : ℝ) ≤ R^2 :=
    FinalRates.radius_sq_bound hC.le (Nat.cast_nonneg _) hRad
  have step : coversAtBound (m+c.fullDim) ((Real.exp 1*Cstar)*(n : ℝ)*Real.log (n : ℝ)) := by
    intro K hK hc hi
    obtain ⟨e,he⟩ := hgaussian m c.fullDim hmn hD hDpower K hK hc hi
    obtain ⟨heK,hec,hei⟩ := affine_body e hK hc hi
    have heV := body_volume_pos heK hei
    have hg : ∀ y : c.FullVec, ‖WithLp.toLp 2 y‖ ≤ 6*(c.fullDim : ℝ)*R →
        (volume (e '' K)).toReal*gamma y/2 ≤ (volume (coordinateFiber (e '' K) y)).toReal := by
      intro y hy
      apply le_trans _ (he y (hy.trans hRadius.le))
      have hy0 : 0 < gamma y := Finset.prod_pos (fun j _ => gamma1_pos _)
      nlinarith [mul_nonneg (show 0 ≤ 1-C₀*(n : ℝ)^(-γ)-1/2 by linarith)
        (mul_nonneg heV.le hy0.le)]
    obtain ⟨Λ,hd,hfull,hcover,hbound⟩ := sections_and_circuits_cover c hm270 hD (e '' K) heK hec heV
      (FinalRates.sectionRadius_pos hC n) hrad hSmall hg κ ρ ε (Real.sqrt (m : ℝ))
      (8*(n : ℝ)*Real.log (n : ℝ)) hρ (Real.sqrt_nonneg _) (by positivity)
      (by
        intro y
        obtain ⟨P,hPn,hPb,hPl,hPt,hPw⟩ := hPattern y
        exact ⟨P,hPn,hPb,hPl,hPw⟩)
      (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hload) hcap hcrit (by
        intro δ s hs
        have hs' : (s.card : ℝ) ≤ (3*(n : ℝ)^2)^c.fullDim := hs.trans (by
          gcongr)
        have ha : ∀ j < c.fullDim, Real.log ((c.alphabetSeq j).card+1 : ℝ) ≤
            Real.log 8+(c.fullDim : ℝ)*Real.log ((c.fullDim : ℝ)+2)+(FinalRates.firstSize n : ℝ)^2 := by
          intro j hj
          simpa only [c.alphabetSeq_fin ⟨j,hj⟩] using hAlphabet ⟨j,hj⟩
        simpa only [Nat.sub_add_cancel hDn] using hcount s c.alphabetSeq hs' ha)
    let := hd
    let := hfull
    have hb : (volume (e '' K)).toReal/ZLattice.covolume Λ volume ≤
        (Real.exp 1*Cstar)*(n : ℝ)*Real.log (n : ℝ) := by
      convert hbound using 1 ; dsimp [ρ] ; ring
    exact pull_back_cover e K Λ hcover hb
  change coversAtBound n ((Real.exp 1*Cstar)*(n : ℝ)*Real.log (n : ℝ))
  simpa only [hmn] using step


end SingleLatticeCovering.Assembly


noncomputable section

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
