import OAI.NumberTheory.GaussianMoat.PosteriorSampling

namespace OAI

universe uIota uOmega uAlpha uBeta uGamma uDelta

namespace GaussianMoat
open scoped BigOperators Classical

noncomputable def incrementWord (z : ℕ → GaussianInt) (L t : ℕ) : Fin L → GaussianInt :=
  fun i => z (t+i.val+1)-z (t+i.val)

lemma incrementWord_sum (z : ℕ → GaussianInt) (L t : ℕ) :
    ∑ i, incrementWord z L t i=z (t+L)-z t := by
  simp only [incrementWord]
  rw [Fin.sum_univ_eq_sum_range (fun i => z (t+i+1)-z (t+i))]
  simpa only [Nat.add_assoc,Nat.add_zero] using
    Finset.sum_range_sub (fun i => z (t+i)) L

lemma block_displacement (z : ℕ → GaussianInt) (L k t u : ℕ)
    (h : ∀ j<k, incrementWord z L (t+j*L)=incrementWord z L (u+j*L)) :
    z (t+k*L)-z t=z (u+k*L)-z u := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hh := ih (fun j hj => h j (by omega))
    have hk := congrArg (fun w : Fin L → GaussianInt => ∑ i, w i) (h k (by omega))
    rw [incrementWord_sum,incrementWord_sum] at hk
    have ht : t+k*L+L=t+(k+1)*L := by ring
    have hu : u+k*L+L=u+(k+1)*L := by ring
    rw [ht,hu] at hk
    linear_combination hh+hk

lemma residue_block_update {ι : Type uIota} (f : ι → GaussianInt) (z : ℕ → GaussianInt)
    (L k t u : ℕ)
    (hQ : (fun i => residueCode (f i) (z t))=(fun i => residueCode (f i) (z u)))
    (hW : ∀ j<k, incrementWord z L (t+j*L)=incrementWord z L (u+j*L)) :
    (fun i => residueCode (f i) (z (t+k*L)))=
      (fun i => residueCode (f i) (z (u+k*L))) := by
  have hd := block_displacement z L k t u hW
  funext i
  have hh := residueCode_add (congrFun hQ i) (congrArg (residueCode (f i)) hd)
  simpa only [add_sub_cancel] using hh

theorem incrementWord_blocks_entropy {Ω : Type uOmega} {ι : Type uIota} [Fintype Ω]
    (p : FinLaw Ω) (t : Ω → ℕ) (z : ℕ → GaussianInt) (f : ι → GaussianInt)
    (L n : ℕ) (hL : 0<L) :
    p.cHf (fun ω => incrementWord z (n*L) (t ω))
      (fun ω i => residueCode (f i) (z (t ω))) ≤
      ∑ j : Fin n, p.cHf (fun ω => incrementWord z L (t ω+j.val*L))
        (fun ω i => residueCode (f i) (z (t ω+j.val*L))) := by
  let W := fun ω (j : Fin n) => incrementWord z L (t ω+j.val*L)
  let Q := fun ω i => residueCode (f i) (z (t ω))
  have hvec : p.cHf (fun ω => incrementWord z (n*L) (t ω)) Q ≤ p.cHf W Q := by
    apply p.cHf_le_of_determined
    intro ω ν h _
    funext i
    let j : Fin n := ⟨i.val/L,(Nat.div_lt_iff_lt_mul hL).mpr i.isLt⟩
    let a : Fin L := ⟨i.val%L,Nat.mod_lt _ hL⟩
    have hh := congrFun (congrFun h j) a
    have he : j.val*L+a.val=i.val := by
      dsimp only [j,a]
      simpa only [Nat.mul_comm] using Nat.div_add_mod i.val L
    simpa only [W,incrementWord,Nat.add_assoc,he] using hh
  apply hvec.trans
  apply p.cHf_blocks_le W Q
  intro j ω ν hW hQ
  apply residue_block_update f z L j.val (t ω) (t ν) hQ
  intro k hk
  have hh := congrFun hW ⟨k,lt_trans hk j.isLt⟩
  simpa only [FinLaw.prefixVar,Equiv.refl_apply,hk,ite_eq_left,Option.some.injEq,W] using hh

noncomputable def boundedWord (z : ℕ → GaussianInt) {D : ℝ}
    (hz : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D) (L t : ℕ) : Fin L → latticeBall D :=
  fun i => ⟨incrementWord z L t i,by
    rw [mem_latticeBall]
    simpa only [incrementWord,map_sub,← dist_eq_norm,dist_comm] using hz (t+i.val)⟩

lemma boundedWord_fibers (z : ℕ → GaussianInt) {D : ℝ}
    (hz : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D) (L t u : ℕ) :
    boundedWord z hz L t=boundedWord z hz L u ↔ incrementWord z L t=incrementWord z L u := by
  constructor
  · intro h
    funext i
    exact congrArg Subtype.val (congrFun h i)
  · intro h
    funext i
    exact Subtype.ext (congrFun h i)

lemma boundedWord_entropy_le {Ω : Type uOmega} [Fintype Ω] (p : FinLaw Ω) (t : Ω → ℕ)
    (z : ℕ → GaussianInt) {D : ℝ} (hz : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D) (L : ℕ) :
    p.Hf (fun ω => incrementWord z L (t ω)) ≤ (L:ℝ)*Real.log (latticeBall D).card := by
  have he : p.Hf (fun ω => incrementWord z L (t ω))=p.Hf (fun ω => boundedWord z hz L (t ω)) := by
    apply p.Hf_eq_of_fibers
    intro ω ν
    exact (boundedWord_fibers z hz L (t ω) (t ν)).symm
  rw [he]
  have h := p.Hf_le_log_card_type (fun ω => boundedWord z hz L (t ω))
  simpa only [Fintype.card_fun,Fintype.card_fin,Fintype.card_coe,Nat.cast_pow,Real.log_pow] using h

@[simp] lemma gaussianResidue_add (π z w : GaussianInt) :
    gaussianResidue π (z+w)=gaussianResidue π z+gaussianResidue π w := rfl
@[simp] lemma gaussianResidue_sub (π z w : GaussianInt) :
    gaussianResidue π (z-w)=gaussianResidue π z-gaussianResidue π w := rfl
@[simp] lemma gaussianResidue_zero (π : GaussianInt) : gaussianResidue π 0=0 := rfl

lemma short_residue_hits_disjoint (π : GaussianInt) (z : ℕ → GaussianInt)
    (hz : Function.Injective z) {D : ℝ} (hD : 0 ≤ D)
    (hs : ∀ t, dist (z t:ℂ) (z (t+1):ℂ) ≤ D) {L : ℕ}
    (hshort : (D*L)^2 < (π.norm:ℝ)) (a t : ℕ)
    (x : GaussianInt ⧸ multiples π) (i j : Fin L)
    (hi : gaussianResidue π (z (t+i.val)-z a)=x)
    (hj : gaussianResidue π (z (t+j.val)-z a)=x) : i=j := by
  by_contra hij
  have hneq : z (t+i.val)≠z (t+j.val) := by
    intro he
    have ht := hz he
    apply hij
    apply Fin.ext
    omega
  have hh := walk_pair_displacement z hD hs t L i.val j.val (by omega) (by omega)
  rw [GaussianInt.toComplex_sub,← dist_eq_norm] at hh
  have hd : dist (z (t+i.val):ℂ) (z (t+j.val):ℂ)^2 < (π.norm:ℝ) := by
    exact (sq_le_sq₀ dist_nonneg (mul_nonneg hD (Nat.cast_nonneg L))).mpr hh |>.trans_lt hshort
  have hres : gaussianResidue π (z (t+i.val))=gaussianResidue π (z (t+j.val)) := by
    simpa only [gaussianResidue_sub,sub_left_inj] using hi.trans hj.symm
  exact not_dvd_sub_of_dist_sq_lt hneq hd ((gaussianResidue_eq _ _ _).mp hres)

lemma short_residue_hit_prob {Ω : Type uOmega} [Fintype Ω] (p : FinLaw Ω)
    (π : GaussianInt) (z : ℕ → GaussianInt) (hz : Function.Injective z)
    {D : ℝ} (hD : 0 ≤ D) (hs : ∀ t, dist (z t:ℂ) (z (t+1):ℂ) ≤ D)
    {L : ℕ} (hshort : (D*L)^2 < (π.norm:ℝ)) (a : ℕ) (t : Ω → ℕ)
    (x : GaussianInt ⧸ multiples π) :
    p.prob (fun ω => ∃ i : Fin L, gaussianResidue π (z (t ω+i.val)-z a)=x) =
      ∑ i : Fin L, p.prob (fun ω => gaussianResidue π (z (t ω+i.val)-z a)=x) := by
  apply p.prob_exists_eq_sum_disjoint
  intro ω i j hi hj
  exact short_residue_hits_disjoint π z hz hD hs hshort a (t ω) x i j hi hj

theorem smoothed_package_hit_lower {Ω : Type uOmega} [Fintype Ω] (p : FinLaw Ω)
    (π : GaussianInt) (z : ℕ → GaussianInt) (hz : Function.Injective z)
    {D c : ℝ} (hD : 0 ≤ D) (hs : ∀ t, dist (z t:ℂ) (z (t+1):ℂ) ≤ D)
    {L N : ℕ} (hshort : (D*L)^2 < (π.norm:ℝ)) (hLN : L ≤ N)
    (herr : (L:ℝ)/(N+1) ≤ c/2) (a : ℕ) (t : Ω → ℕ)
    (x : GaussianInt ⧸ multiples π)
    (hfloor : c ≤ (p.joint (fun _ => FinLaw.uniform (Fin (N+1)))).prob
      (fun v => gaussianResidue π (z (t v.1+v.2.val)-z a)=x)) :
    (L:ℝ)*c/2 ≤ (p.joint (fun _ => FinLaw.uniform (Fin (N+1)))).prob
      (fun v => ∃ i : Fin L, gaussianResidue π (z (t v.1+v.2.val+i.val)-z a)=x) := by
  rw [short_residue_hit_prob _ π z hz hD hs hshort a]
  have hh (i : Fin L) : c/2 ≤
      (p.joint (fun _ => FinLaw.uniform (Fin (N+1)))).prob
        (fun v => gaussianResidue π (z (t v.1+v.2.val+i.val)-z a)=x) := by
    have hp := p.smoothing_prob t N i.val (by omega)
      (fun b => gaussianResidue π (z b-z a)=x)
    have he : (i.val:ℝ)/(N+1) ≤ c/2 := by
      apply le_trans _ herr
      exact div_le_div_of_nonneg_right (by exact_mod_cast i.isLt.le) (by positivity)
    linarith only [hp,hfloor,he]
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hh i)
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_div_assoc] using h

lemma true_residue_no_hit (π : GaussianInt) (z : ℕ → GaussianInt)
    (havoid : ∀ t, ¬π ∣ z t) (a t L : ℕ) :
    ¬∃ i : Fin L, gaussianResidue π (z (t+i.val)-z a) = -gaussianResidue π (z a) := by
  rintro ⟨i,hi⟩
  have hh : gaussianResidue π (z (t+i.val))=gaussianResidue π 0 := by
    rw [gaussianResidue_sub] at hi
    rw [gaussianResidue_zero]
    exact sub_eq_neg_self.mp hi
  have hd := (gaussianResidue_eq _ _ _).mp hh
  simp only [sub_zero] at hd
  exact havoid _ hd

namespace FinLaw
variable {Ω : Type uOmega} {α : Type uAlpha} {β : Type uBeta} {γ : Type uGamma} {δ : Type uDelta} [Fintype Ω]

lemma cHf_congr_fibers (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) (C : Ω → γ) (D : Ω → δ)
    (hX : ∀ ω ν, X ω=X ν ↔ Y ω=Y ν) (hC : ∀ ω ν, C ω=C ν ↔ D ω=D ν) :
    p.cHf X C=p.cHf Y D := by
  unfold cHf
  rw [p.Hf_eq_of_fibers C D hC]
  congr 1
  apply p.Hf_eq_of_fibers
  intro ω ν
  simp only [Prod.mk.injEq,hX,hC]

end FinLaw

lemma residueCode_vector_fibers {ι : Type uIota} (f : ι → GaussianInt) (x y : GaussianInt) :
    (fun i => residueCode (f i) x)=(fun i => residueCode (f i) y) ↔
      (fun i => gaussianResidue (f i) x)=(fun i => gaussianResidue (f i) y) := by
  simp only [funext_iff,residueCode_eq,gaussianResidue_eq]

theorem word_residue_smoothing {Ω : Type uOmega} {ι : Type uIota} [Fintype Ω] [Fintype ι]
    (p : FinLaw Ω) (t : Ω → ℕ) (z : ℕ → GaussianInt) {D : ℝ}
    (hz : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D)
    (f : ι → GaussianInt) (hf : ∀ i, f i≠0) (L N a : ℕ) (ha : a≤N) :
    let P := p.joint (fun _ => FinLaw.uniform (Fin (N+1)))
    P.cHf (fun v => incrementWord z L (t v.1+v.2.val+a))
      (fun v i => residueCode (f i) (z (t v.1+v.2.val+a))) ≤
    P.cHf (fun v => incrementWord z L (t v.1+v.2.val))
      (fun v i => residueCode (f i) (z (t v.1+v.2.val)))+
      2*Real.binEntropy ((a:ℝ)/(N+1))+
      ((a:ℝ)/(N+1))*((L:ℝ)*Real.log (latticeBall D).card+
        2*∑ i, Real.log (f i).norm.natAbs) := by
  let (i : ι) : Finite (GaussianInt ⧸ multiples (f i)) := finite_gaussianResidue (hf i)
  let (i : ι) : Fintype (GaussianInt ⧸ multiples (f i)) := Fintype.ofFinite _
  dsimp only
  let P := p.joint (fun _ => FinLaw.uniform (Fin (N+1)))
  have he (u : Ω × Fin (N+1) → ℕ) :
      P.cHf (fun v => incrementWord z L (u v)) (fun v i => residueCode (f i) (z (u v))) =
      P.condH (fun v => boundedWord z hz L (u v)) (fun v i => gaussianResidue (f i) (z (u v))) := by
    rw [show P.condH (fun v => boundedWord z hz L (u v))
      (fun v i => gaussianResidue (f i) (z (u v))) =
      P.cHf (fun v => boundedWord z hz L (u v))
      (fun v i => gaussianResidue (f i) (z (u v))) by
        simp only [FinLaw.condH,FinLaw.cHf,FinLaw.Hf_eq_H]]
    apply P.cHf_congr_fibers
    · intro v w; exact (boundedWord_fibers z hz L (u v) (u w)).symm
    · intro v w; exact residueCode_vector_fibers f _ _
  have h := p.smoothing_condH t N a ha (boundedWord z hz L)
    (fun t i => gaussianResidue (f i) (z t))
  have hc : Real.log (Fintype.card ((i : ι) → GaussianInt ⧸ multiples (f i))) =
      ∑ i, Real.log (f i).norm.natAbs := by
    rw [Fintype.card_pi,Nat.cast_prod,Real.log_prod]
    · apply Finset.sum_congr rfl
      intro i _
      rw [← Nat.card_eq_fintype_card,multiples_index (hf i)]
    · intro i _
      exact_mod_cast Fintype.card_ne_zero
  change P.cHf _ _ ≤ P.cHf _ _+_+_
  rw [he,he]
  simpa only [Fintype.card_fun,Fintype.card_fin,Fintype.card_coe,Nat.cast_pow,
    Real.log_pow,hc] using h

end GaussianMoat

end OAI
