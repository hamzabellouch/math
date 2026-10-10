import OAI.Analysis.FreeGroupFactor.FiniteActive

namespace OAI

noncomputable section

universe uA uG uι

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff ENNReal

attribute [local instance] Classical.propDecidable

namespace FreeGroupFactorMain.Generation

 theorem norm_comp_sub_le {A : Type uA} [CStarAlgebra A]
    (α β : A ≃⋆ₐ[ℂ] A) (x : A) :
    ‖α (β x)-x‖ ≤ ‖β x-x‖+‖α x-x‖ := by
  have he : α (β x)-x = α (β x-x)+(α x-x) := by rw [map_sub]; abel
  rw [he]
  exact (norm_add_le _ _).trans_eq (by rw [StarAlgEquiv.norm_map])

 theorem twoNorm_comp_sub_le {G : Type uG} [Group G]
    (α β : groupVonNeumann G ≃⋆ₐ[ℂ] groupVonNeumann G)
    (ht : ∀ T, canonicalTrace (α T) = canonicalTrace T)
    (x y : groupVonNeumann G) :
    twoNorm (α (β x)-y) ≤ twoNorm (β x-x)+twoNorm (α x-y) := by
  have he : α (β x)-y = α (β x-x)+(α x-y) := by rw [map_sub]; abel
  rw [he]
  exact (twoNorm_add_le _ _).trans_eq (by rw [twoNorm_iso α ht])

 theorem twoNorm_map_sub_fixed {G : Type uG} [Group G]
    (α : groupVonNeumann G ≃⋆ₐ[ℂ] groupVonNeumann G)
    (ht : ∀ T, canonicalTrace (α T) = canonicalTrace T)
    (x y : groupVonNeumann G) (hy : α y = y) :
    twoNorm (α x-y) = twoNorm (x-y) := by
  calc
    twoNorm (α x-y) = twoNorm (α (x-y)) := by rw [map_sub,hy]
    _ = twoNorm (x-y) := twoNorm_iso α ht _

 theorem mapTuple_dist_lt {A : Type uA} [CStarAlgebra A] {ι : Type uι} [Fintype ι]
    (α : A ≃⋆ₐ[ℂ] A) (U : ι → unitary A) {ε : ℝ} (hε : 0 < ε)
    (h : ∀ i, ‖α (U i : A)-(U i : A)‖ < ε) : dist (mapTuple α U) U < ε := by
  apply (dist_pi_lt_iff hε).mpr
  intro i
  change dist (α (U i : A)) (U i : A) < ε
  rw [dist_eq_norm]
  exact h i

theorem conjugate_fix {A : Type uA} [CStarAlgebra A]
    (α Ψ : A ≃⋆ₐ[ℂ] A) (x y : A) (hΨ : Ψ x = y) (hα : α x = x) :
    Ψ (α (Ψ.symm y)) = y := by
  rw [← hΨ,Ψ.symm_apply_apply,hα]

theorem conjugate_norm_sub {A : Type uA} [CStarAlgebra A]
    (α Ψ : A ≃⋆ₐ[ℂ] A) (x : A) (hx : Ψ x = x) :
    ‖Ψ (α (Ψ.symm x))-x‖ = ‖α x-x‖ := by
  conv_lhs => rw [← hx,Ψ.symm_apply_apply,← map_sub,StarAlgEquiv.norm_map]

theorem conjugate_twoNorm_sub {G : Type uG} [Group G]
    (α Ψ : groupVonNeumann G ≃⋆ₐ[ℂ] groupVonNeumann G)
    (ht : ∀ T, canonicalTrace (Ψ T) = canonicalTrace T)
    (x y z : groupVonNeumann G) (hx : Ψ x = x) (hy : Ψ y = z) :
    twoNorm (Ψ (α (Ψ.symm x))-z) = twoNorm (α x-y) := by
  conv_lhs => rw [← hx,Ψ.symm_apply_apply,← hy,← map_sub,twoNorm_iso Ψ ht]

end FreeGroupFactorMain.Generation

namespace FreeGroupFactorMain.InfiniteGeneration
open Generation

abbrev Index := Option (Fin 3 ⊕ ℕ)
abbrev Group := FreeGroup Index
abbrev M := groupVonNeumann Group
abbrev Tuple := Fin 3 → unitary M

def initial : Tuple := fun i => generatorUnitary (some (Sum.inl i))
def extra (q : Option ℕ) : unitary M :=
  generatorUnitary (q.elim none (fun k => some (Sum.inr k)))

theorem word_initial (g : FreeGroup (Fin 3)) :
    word initial g = groupUnitary (FreeGroup.map (fun i => some (Sum.inl i)) g) := by
  have he : word initial = (groupUnitaryHom Group).comp
      (FreeGroup.map (fun i => some (Sum.inl i))) := by
    apply FreeGroup.ext_hom
    intro i
    simp only [word_of,MonoidHom.comp_apply,FreeGroup.map.of]
    rfl
  exact DFunLike.congr_fun he g

theorem permutation_iso (e : Index ≃ Index) :
    ∃ Φ : M ≃⋆ₐ[ℂ] M, (∀ T, canonicalTrace (Φ T) = canonicalTrace T) ∧
      ∀ i, Φ (generatorUnitary i : M) = (generatorUnitary (e i) : M) := by
  obtain ⟨Φ,ht,_hc,_hci,hg⟩ := gaugedIso (FreeGroup.freeGroupCongr e) (1 : Group →* unitary ℂ)
  refine ⟨Φ,ht,?_⟩
  intro i
  have hh := hg (FreeGroup.of i)
  simp only [MonoidHom.one_apply,Submonoid.coe_one,one_smul] at hh
  change Φ (groupUnitary (FreeGroup.of i)) = groupUnitary (FreeGroup.map e (FreeGroup.of i)) at hh
  simpa only [FreeGroup.map.of,generatorUnitary] using hh

theorem swapped_extra_iso (k : ℕ) :
    ∃ Ψ : M ≃⋆ₐ[ℂ] M, (∀ T, canonicalTrace (Ψ T) = canonicalTrace T) ∧
      (∀ i, Ψ (initial i : M) = (initial i : M)) ∧
      Ψ (extra none : M) = (extra (some k) : M) ∧
      Ψ (extra (some k) : M) = (extra none : M) ∧
      ∀ j, j ≠ k → Ψ (extra (some j) : M) = (extra (some j) : M) := by
  let e : Index ≃ Index := Equiv.swap none (some (Sum.inr k))
  obtain ⟨Ψ,hΨt,hΨ⟩ := permutation_iso e
  have hΨA (i : Fin 3) : Ψ (initial i : M) = (initial i : M) := by
    change Ψ (generatorUnitary (some (Sum.inl i) : Index) : M) = _
    rw [hΨ]
    simp [e,Equiv.swap_apply_of_ne_of_ne,initial]
  have hΨ0 : Ψ (extra none : M) = (extra (some k) : M) := by
    change Ψ (generatorUnitary (none : Index) : M) = _
    rw [hΨ]
    simp [e,extra]
  have hΨk : Ψ (extra (some k) : M) = (extra none : M) := by
    change Ψ (generatorUnitary (some (Sum.inr k) : Index) : M) = _
    rw [hΨ]
    simp [e,extra]
  have hΨj (j : ℕ) (hj : j ≠ k) : Ψ (extra (some j) : M) = (extra (some j) : M) := by
    change Ψ (generatorUnitary (some (Sum.inr j) : Index) : M) = _
    rw [hΨ]
    simp [e,Equiv.swap_apply_of_ne_of_ne,hj,extra]
  exact ⟨Ψ,hΨt,hΨA,hΨ0,hΨk,hΨj⟩

theorem one_step_extra_of_none
    (hone : ∀ ε : ℝ, 0 < ε → ∃ α : M ≃⋆ₐ[ℂ] M,
      (∀ T, canonicalTrace (α T) = canonicalTrace T) ∧
      (∀ k : ℕ, α (extra (some k) : M) = (extra (some k) : M)) ∧
      ∃ w : FreeGroup (Fin 3),
        (∀ i, ‖α (initial i : M)-(initial i : M)‖ < ε) ∧
        twoNorm (α (word initial w)-(extra none : M)) < ε)
    (q : Option ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ α : M ≃⋆ₐ[ℂ] M, (∀ T, canonicalTrace (α T) = canonicalTrace T) ∧
      (∀ r : Option ℕ, r ≠ q → α (extra r : M) = (extra r : M)) ∧
      ∃ w : FreeGroup (Fin 3),
        (∀ i, ‖α (initial i : M)-(initial i : M)‖ < ε) ∧
        twoNorm (α (word initial w)-(extra q : M)) < ε := by
  obtain ⟨α,ht,hfix,w,hA,hw⟩ := hone ε hε
  cases q with
  | none =>
    refine ⟨α,ht,?_,w,hA,hw⟩
    rintro (_|k) hk
    · exact (hk rfl).elim
    · exact hfix k
  | some k =>
    obtain ⟨Ψ,hΨt,hΨA,hΨ0,hΨk,hΨj⟩ := swapped_extra_iso k
    have hΨtuple : mapTuple Ψ initial = initial := by
      funext i
      exact Subtype.ext (hΨA i)
    have hΨword : Ψ (word initial w) = word initial w := by
      rw [← word_mapTuple,hΨtuple]
    refine ⟨(Ψ.symm.trans α).trans Ψ,?_,?_,w,?_,?_⟩
    · intro T
      simp only [StarAlgEquiv.trans_apply,hΨt,ht,trace_symm Ψ hΨt]
    · intro r hr
      change Ψ (α (Ψ.symm (extra r : M))) = (extra r : M)
      cases r with
      | none => exact conjugate_fix α Ψ _ _ hΨk (hfix k)
      | some j =>
        have hj : j ≠ k := fun he => hr (congrArg some he)
        exact conjugate_fix α Ψ _ _ (hΨj j hj) (hfix j)
    · intro i
      change ‖Ψ (α (Ψ.symm (initial i : M)))-(initial i : M)‖ < ε
      rw [conjugate_norm_sub α Ψ _ (hΨA i)]
      exact hA i
    · change twoNorm (Ψ (α (Ψ.symm (word initial w)))-(extra (some k) : M)) < ε
      rw [conjugate_twoNorm_sub α Ψ hΨt _ _ _ hΨword hΨ0]
      exact hw

end FreeGroupFactorMain.InfiniteGeneration

namespace FreeGroupFactorMain.Generation
variable {G : Type uG} [Group G] {ι : Type uι}

theorem word_twoNorm_finite_bound (g : FreeGroup ι) :
    ∃ (s : Finset ι) (K : ℝ), 0 ≤ K ∧
      ∀ (U V : ι → unitary (groupVonNeumann G)) (δ : ℝ), 0 ≤ δ →
        (∀ j ∈ s, twoNorm ((U j : groupVonNeumann G)-(V j : groupVonNeumann G)) ≤ δ) →
        twoNorm (word U g-word V g) ≤ K*δ := by
  classical
  induction g using FreeGroup.induction_on with
  | one =>
    refine ⟨∅,0,le_rfl,?_⟩
    intro U V δ _hδ _hUV
    simp only [map_one,sub_self,twoNorm_zero,zero_mul,le_refl]
  | of j =>
    refine ⟨{j},1,by norm_num,?_⟩
    intro U V δ _hδ hUV
    simpa only [word_of,one_mul] using hUV j (Finset.mem_singleton_self j)
  | inv_of j ih =>
    obtain ⟨s,K,hK,hb⟩ := ih
    refine ⟨s,K,hK,?_⟩
    intro U V δ hδ hUV
    rw [word_inv,word_inv,← star_sub,twoNorm_star]
    exact hb U V δ hδ hUV
  | mul g h hg hh =>
    obtain ⟨s,K,hK,hb⟩ := hg
    obtain ⟨t,L,hL,hl⟩ := hh
    refine ⟨s ∪ t,K+L,add_nonneg hK hL,?_⟩
    intro U V δ hδ hUV
    rw [map_mul,map_mul]
    exact (twoNorm_mul_sub_le (FreeGroup.lift U g) (FreeGroup.lift U h)
      (FreeGroup.lift V g) (FreeGroup.lift V h)).trans (by
      simpa only [add_mul,word,MonoidHom.comp_apply,Submonoid.subtype_apply] using
        add_le_add (hb U V δ hδ (fun j hj => hUV j (Finset.mem_union_left _ hj)))
          (hl U V δ hδ (fun j hj => hUV j (Finset.mem_union_right _ hj))))

theorem poly_twoNorm_finite_bound (p : FreeGroup ι →₀ ℂ) :
    ∃ (s : Finset ι) (K : ℝ), 0 ≤ K ∧
      ∀ (U V : ι → unitary (groupVonNeumann G)) (δ : ℝ), 0 ≤ δ →
        (∀ j ∈ s, twoNorm ((U j : groupVonNeumann G)-(V j : groupVonNeumann G)) ≤ δ) →
        twoNorm (poly U p-poly V p) ≤ K*δ := by
  classical
  induction p using Finsupp.induction_linear with
  | zero =>
    refine ⟨∅,0,le_rfl,?_⟩
    intro U V δ _hδ _hUV
    simp only [poly_zero,sub_self,twoNorm_zero,zero_mul,le_refl]
  | add p q ihp ihq =>
    obtain ⟨s,K,hK,hb⟩ := ihp
    obtain ⟨t,L,hL,hl⟩ := ihq
    refine ⟨s ∪ t,K+L,add_nonneg hK hL,?_⟩
    intro U V δ hδ hUV
    simp only [poly_add]
    have he : poly U p+poly U q-(poly V p+poly V q) =
        (poly U p-poly V p)+(poly U q-poly V q) := by abel
    rw [he]
    exact (twoNorm_add_le _ _).trans (by
      simpa only [add_mul] using
        add_le_add (hb U V δ hδ (fun j hj => hUV j (Finset.mem_union_left _ hj)))
          (hl U V δ hδ (fun j hj => hUV j (Finset.mem_union_right _ hj))))
  | single g c =>
    obtain ⟨s,K,hK,hb⟩ := word_twoNorm_finite_bound (G := G) g
    refine ⟨s,‖c‖*K,mul_nonneg (norm_nonneg _) hK,?_⟩
    intro U V δ hδ hUV
    simp only [poly_single,← smul_sub,twoNorm_smul]
    exact (mul_le_mul_of_nonneg_left (hb U V δ hδ hUV) (norm_nonneg c)).trans_eq
      (mul_assoc _ _ _).symm

end FreeGroupFactorMain.Generation

namespace FreeGroupFactorMain.InfiniteGeneration
open Generation

 theorem finite_word_continuity (s : Finset (Option ℕ)) (w : Option ℕ → FreeGroup (Fin 3))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ U : Tuple, dist U initial < δ →
      ∀ j ∈ s, ‖word U (w j)-word initial (w j)‖ < ε := by
  have hc : Continuous (fun U : Tuple => fun j : s => word U (w j)) :=
    continuous_pi (fun j => word_continuous (w j))
  obtain ⟨δ,hδ,hd⟩ := Metric.continuousAt_iff.mp hc.continuousAt ε hε
  refine ⟨δ,hδ,?_⟩
  intro U hU j hj
  have hh := (dist_pi_lt_iff hε).mp (hd hU) (⟨j,hj⟩ : s)
  rwa [dist_eq_norm] at hh

theorem finite_absorption
    (hone : ∀ (q : Option ℕ) (ε : ℝ), 0 < ε →
      ∃ α : M ≃⋆ₐ[ℂ] M, (∀ T, canonicalTrace (α T) = canonicalTrace T) ∧
        (∀ r : Option ℕ, r ≠ q → α (extra r : M) = (extra r : M)) ∧
        ∃ w : FreeGroup (Fin 3),
          (∀ i, ‖α (initial i : M)-(initial i : M)‖ < ε) ∧
          twoNorm (α (word initial w)-(extra q : M)) < ε)
    (s : Finset (Option ℕ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ α : M ≃⋆ₐ[ℂ] M, (∀ T, canonicalTrace (α T) = canonicalTrace T) ∧
      (∀ r, r ∉ s → α (extra r : M) = (extra r : M)) ∧
      ∃ w : Option ℕ → FreeGroup (Fin 3),
        (∀ i, ‖α (initial i : M)-(initial i : M)‖ < ε) ∧
        ∀ j ∈ s, twoNorm (α (word initial (w j))-(extra j : M)) < ε := by
  classical
  induction s using Finset.induction_on generalizing ε with
  | empty =>
    refine ⟨StarAlgEquiv.refl ℂ M,fun _ => rfl,fun _ _ => rfl,fun _ => 1,?_,?_⟩
    · intro i
      change ‖(initial i : M)-(initial i : M)‖ < ε
      simpa only [sub_self,norm_zero] using hε
    · intro j hj
      exact (Finset.notMem_empty j hj).elim
  | @insert j s hj ih =>
    obtain ⟨α,hαt,hαfix,w,hαA,hαw⟩ := ih (ε/2) (half_pos hε)
    obtain ⟨δ,hδ,hd⟩ := finite_word_continuity s w (half_pos hε)
    let η := min (ε/2) δ
    have hη : 0 < η := lt_min (half_pos hε) hδ
    obtain ⟨β,hβt,hβfix,v,hβA,hβv⟩ := hone j η hη
    have hbd := mapTuple_dist_lt β initial hη hβA
    refine ⟨β.trans α,?_,?_,Function.update w j v,?_,?_⟩
    · intro T
      simp only [StarAlgEquiv.trans_apply,hαt,hβt]
    · intro r hr
      have hrs : r ∉ s := fun hh => hr (Finset.mem_insert_of_mem hh)
      have hrj : r ≠ j := fun hh => hr (hh ▸ Finset.mem_insert_self j s)
      simp only [StarAlgEquiv.trans_apply,hβfix r hrj,hαfix r hrs]
    · intro i
      change ‖α (β (initial i : M))-(initial i : M)‖ < ε
      apply (norm_comp_sub_le α β (initial i : M)).trans_lt
      have hh := (hβA i).trans_le (min_le_left _ _)
      linarith [hαA i]
    · intro r hr
      rcases Finset.mem_insert.mp hr with hrj | hrs
      · subst r
        rw [Function.update_self]
        change twoNorm (α (β (word initial v))-(extra j : M)) < ε
        rw [twoNorm_map_sub_fixed α hαt _ _ (hαfix j hj)]
        exact hβv.trans_le ((min_le_left _ _).trans (by linarith))
      · by_cases hrj : r = j
        · subst r
          exact (hj hrs).elim
        rw [Function.update_of_ne hrj]
        change twoNorm (α (β (word initial (w r)))-(extra r : M)) < ε
        apply (twoNorm_comp_sub_le α β hαt _ _).trans_lt
        have hh := hd (mapTuple β initial) (hbd.trans_le (min_le_right _ _)) r hrs
        rw [word_mapTuple] at hh
        have hh' := (twoNorm_le_norm _).trans_lt hh
        linarith [hαw r hrs]

 def orbit : Set Tuple := {U | ∃ Φ : M ≃⋆ₐ[ℂ] M,
    (∀ T, canonicalTrace (Φ T) = canonicalTrace T) ∧ U = mapTuple Φ initial}

 theorem orbit_nonempty : orbit.Nonempty := by
  refine ⟨mapTuple (StarAlgEquiv.refl ℂ M) initial,StarAlgEquiv.refl ℂ M,?_,rfl⟩
  intro T
  rfl

 def extraLabel : Index → Option ℕ := fun j => j.elim none (Sum.elim (fun _ => none) some)
 def replacement (w : Option ℕ → FreeGroup (Fin 3)) : Index → FreeGroup (Fin 3) :=
  fun j => j.elim (w none) (Sum.elim FreeGroup.of (fun k => w (some k)))

 theorem orbit_step
    (hfinite : ∀ (s : Finset (Option ℕ)) (ε : ℝ), 0 < ε →
      ∃ α : M ≃⋆ₐ[ℂ] M, (∀ T, canonicalTrace (α T) = canonicalTrace T) ∧
        (∀ r, r ∉ s → α (extra r : M) = (extra r : M)) ∧
        ∃ w : Option ℕ → FreeGroup (Fin 3),
          (∀ i, ‖α (initial i : M)-(initial i : M)‖ < ε) ∧
          ∀ j ∈ s, twoNorm (α (word initial (w j))-(extra j : M)) < ε)
    (Φ : M ≃⋆ₐ[ℂ] M) (ht : ∀ T, canonicalTrace (Φ T) = canonicalTrace T)
    (s : Finset Index) {θ : ℝ} (hθ : 0 < θ) :
    ∃ V ∈ orbit, dist V (mapTuple Φ initial) < θ ∧
      ∃ w : Index → FreeGroup (Fin 3), ∀ j ∈ s,
        twoNorm ((wordTuple V w j : M)-(mapTuple Φ generatorUnitary j : M)) < θ := by
  classical
  obtain ⟨α,hαt,_hfix,w,hA,hw⟩ := hfinite (s.image extraLabel) θ hθ
  let V : Tuple := mapTuple (α.trans Φ) initial
  have hdist : dist V (mapTuple Φ initial) < θ := by
    apply (dist_pi_lt_iff hθ).mpr
    intro i
    change dist (Φ (α (initial i : M))) (Φ (initial i : M)) < θ
    have hnorm (T : M) : ‖Φ T‖ = ‖T‖ :=
      NonUnitalStarAlgHom.norm_map Φ.toStarAlgHom Φ.injective T
    rw [dist_eq_norm, ← map_sub, hnorm]
    exact hA i
  refine ⟨V,⟨α.trans Φ,?_,rfl⟩,hdist,replacement w,?_⟩
  · intro T
    simp only [StarAlgEquiv.trans_apply,ht,hαt]
  · intro j hj
    have hex : extraLabel j ∈ s.image extraLabel := Finset.mem_image.mpr ⟨j,hj,rfl⟩
    cases j with
    | none =>
      change twoNorm (word V (w none)-Φ (extra none : M)) < θ
      rw [show V = mapTuple (α.trans Φ) initial from rfl,word_mapTuple,
        StarAlgEquiv.trans_apply,← map_sub,twoNorm_iso Φ ht]
      exact hw none hex
    | some j =>
      cases j with
      | inl i =>
        change twoNorm ((V i : M)-Φ (initial i : M)) < θ
        have hh := (dist_pi_lt_iff hθ).mp hdist i
        change dist (V i : M) (Φ (initial i : M)) < θ at hh
        rw [dist_eq_norm] at hh
        exact (twoNorm_le_norm _).trans_lt hh
      | inr k =>
        change twoNorm (word V (w (some k))-Φ (extra (some k) : M)) < θ
        rw [show V = mapTuple (α.trans Φ) initial from rfl,word_mapTuple,
          StarAlgEquiv.trans_apply,← map_sub,twoNorm_iso Φ ht]
        exact hw (some k) hex

 theorem orbit_local_approximation
    (hstep : ∀ (Φ : M ≃⋆ₐ[ℂ] M), (∀ T, canonicalTrace (Φ T) = canonicalTrace T) →
      ∀ (s : Finset Index) (θ : ℝ), 0 < θ →
        ∃ V ∈ orbit, dist V (mapTuple Φ initial) < θ ∧
          ∃ w : Index → FreeGroup (Fin 3), ∀ j ∈ s,
            twoNorm ((wordTuple V w j : M)-(mapTuple Φ generatorUnitary j : M)) < θ)
    (U : Tuple) (hU : U ∈ orbit) (δ : ℝ) (hδ : 0 < δ)
    (g : Group) (ε : ℝ) (hε : 0 < ε) :
    ∃ V ∈ orbit, dist V U < δ ∧ ∃ p : FreeGroup (Fin 3) →₀ ℂ,
      dist (groupL2 (poly V p)) (lp.single 2 g (1 : ℂ)) < ε := by
  classical
  obtain ⟨Φ,ht,rfl⟩ := hU
  obtain ⟨p,hp⟩ := automorphism_poly_dense Φ ht (groupUnitary g) (half_pos hε)
  obtain ⟨s,K,hK,hbound⟩ := poly_twoNorm_finite_bound (G := Group) p
  let θ := min δ (ε/(2*(K+1)))
  have hθ : 0 < θ := lt_min hδ (div_pos hε (by positivity))
  obtain ⟨V,hV,hd,w,hw⟩ := hstep Φ ht s θ hθ
  refine ⟨V,hV,hd.trans_le (min_le_left _ _),substitute w p,?_⟩
  have hb := hbound (wordTuple V w) (mapTuple Φ generatorUnitary) θ hθ.le (fun j hj => (hw j hj).le)
  have hθe : θ*(2*(K+1)) ≤ ε :=
    (le_div_iff₀ (by positivity : 0 < 2*(K+1))).mp (min_le_right _ _)
  have hKe : K*θ < ε/2 := by nlinarith
  rw [dist_eq_norm,← groupL2_groupUnitary g,← map_sub]
  change twoNorm (poly V (substitute w p)-groupUnitary g) < ε
  rw [poly_substitute]
  have he : poly (wordTuple V w) p-groupUnitary g =
      (poly (wordTuple V w) p-poly (mapTuple Φ generatorUnitary) p)+
      (poly (mapTuple Φ generatorUnitary) p-groupUnitary g) := by abel
  rw [he]
  exact (twoNorm_add_le _ _).trans_lt (by linarith)

 theorem orbit_trace (U : Tuple) (hU : U ∈ orbit) (g : FreeGroup (Fin 3)) :
    canonicalTrace (word U g) = if g = 1 then 1 else 0 := by
  classical
  obtain ⟨Φ,ht,rfl⟩ := hU
  rw [word_mapTuple,ht,word_initial,canonicalTrace_groupUnitary]
  have hinj : Function.Injective (fun i : Fin 3 => (some (Sum.inl i) : Index)) :=
    Option.some_injective _ |>.comp Sum.inl_injective
  have hi : FreeGroup.map (fun i : Fin 3 => (some (Sum.inl i) : Index)) g = 1 ↔ g = 1 := by
    rw [← (FreeGroup.map (fun i : Fin 3 => (some (Sum.inl i) : Index))).map_one]
    exact (FreeGroup.map_injective hinj).eq_iff
  simp only [hi]

 theorem closure_orbit_trace (U : Tuple) (hU : U ∈ closure orbit) (g : FreeGroup (Fin 3)) :
    canonicalTrace (word U g) = if g = 1 then 1 else 0 := by
  classical
  have hc : Continuous (fun V : Tuple => canonicalTrace (word V g)) :=
    (canonicalTraceCLM (G := Group)).continuous.comp (word_continuous g)
  have hclosed : IsClosed {V : Tuple | canonicalTrace (word V g) = if g = 1 then 1 else 0} :=
    isClosed_eq hc continuous_const
  exact (closure_minimal (fun V hV => orbit_trace V hV g) hclosed) hU

 theorem generating_haar_tuple
    (hlocal : ∀ U ∈ orbit, ∀ δ : ℝ, 0 < δ → ∀ g : Group, ∀ ε : ℝ, 0 < ε →
      ∃ V ∈ orbit, dist V U < δ ∧ ∃ p : FreeGroup (Fin 3) →₀ ℂ,
        dist (groupL2 (poly V p)) (lp.single 2 g (1 : ℂ)) < ε) :
    ∃ U : Tuple,
      (∀ g : FreeGroup (Fin 3), canonicalTrace (word U g) = if g = 1 then 1 else 0) ∧
      ⊤ ≤ (Submodule.span ℂ (Set.range (fun g => groupL2 (word U g)))).topologicalClosure := by
  classical
  obtain ⟨U,hU,happrox⟩ := baire_local_approximation orbit orbit_nonempty
    (fun p U => groupL2 (poly U p))
    (fun p => (groupL2 (G := Group)).continuous.comp (poly_continuous p))
    (fun g : Group => lp.single 2 g (1 : ℂ)) hlocal
  exact ⟨U,closure_orbit_trace U hU,total_of_poly_approx U happrox⟩

end FreeGroupFactorMain.InfiniteGeneration

end

end OAI
