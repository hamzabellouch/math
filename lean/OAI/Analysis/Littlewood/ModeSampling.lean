import OAI.Analysis.Littlewood.SamplingEnergy

namespace OAI

universe uP

namespace AsymptoticallyMinimalLittlewood.Sampling
noncomputable section
open scoped BigOperators Topology ContDiff ComplexConjugate
open MeasureTheory Filter Complex QuadraticTail

lemma realPhase_mul_conj (x y : ℝ) :
    realPhase x*conj (realPhase y)=realPhase (x-y) := by
  rw [realPhase,realPhase,realPhase,← Complex.exp_conj,← Complex.exp_add]
  congr 1
  simp only [map_mul,Complex.conj_I,Complex.conj_ofReal,Complex.ofReal_sub]
  ring

lemma realPhase_zero : realPhase 0=1 := by simp [realPhase]

def modeSum {P : Type uP} [Fintype P] (g : P → ℝ → ℂ) (c : P → ℂ)
    (lam b d : P → ℝ) (N : ℕ) (k : Fin N) : ℂ :=
  ∑ i, c i*realPhase (2*Real.pi*N*d i)*g i ((k : ℝ)/N)*phase (lam i/N) (-b i) k

lemma norm_sq_modeSum {P : Type uP} [Fintype P] (g : P → ℝ → ℂ) (c : P → ℂ)
    (lam b d : P → ℝ) (N : ℕ) :
    (((∑ k : Fin N, ‖modeSum g c lam b d N k‖^2)/(N : ℝ) : ℝ) : ℂ)=
      ∑ i, ∑ j, (c i*conj (c j))*realPhase (2*Real.pi*N*(d i-d j))*
        finiteAverage (fun x ↦ g i x*conj (g j x)) N (lam i-lam j) (b i-b j) := by
  classical
  simp only [Complex.ofReal_div,Complex.ofReal_sum,Complex.ofReal_pow]
  have he (z : ℂ) : (‖z‖ : ℂ)^2=z*conj z := by
    rw [Complex.mul_conj,Complex.normSq_eq_norm_sq,Complex.ofReal_pow]
  simp_rw [he]
  simp only [modeSum,map_sum,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := Finset.univ (α := Fin N))]
  simp only [Finset.sum_div,finiteAverage,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  simp only [map_mul,Complex.ofReal_natCast]
  have hp := phase_mul_conj (lam i/N) (-b i) (lam j/N) (-b j) (k : ℝ)
  rw [← sub_div,show -b i - -b j= -(b i-b j) by ring] at hp
  have hd := realPhase_mul_conj (2*Real.pi*N*d i) (2*Real.pi*N*d j)
  rw [show 2*Real.pi*N*d i-2*Real.pi*N*d j=2*Real.pi*N*(d i-d j) by ring] at hd
  calc
    _ = (c i*conj (c j))*(realPhase (2*Real.pi*N*d i)*conj (realPhase (2*Real.pi*N*d j)))*
      (g i ((k : ℝ)/N)*conj (g j ((k : ℝ)/N)))*
      (phase (lam i/N) (-b i) k*conj (phase (lam j/N) (-b j) k))/(N : ℂ) := by ring
    _ = _ := by rw [hd,hp]; ring

lemma amplitude_pair_compact {g h : ℝ → ℂ} (hg : HasCompactSupport g) :
    HasCompactSupport (fun x ↦ g x*conj (h x)) := hg.mul_right

lemma amplitude_pair_smooth {g h : ℝ → ℂ} (hg : ContDiff ℝ ∞ g)
    (hh : ContDiff ℝ ∞ h) : ContDiff ℝ ∞ (fun x ↦ g x*conj (h x)) :=
  hg.mul (Complex.conjCLE.contDiff.comp hh)

lemma amplitude_pair_support {g h : ℝ → ℂ} (hg : tsupport g⊆Set.Ioo (0:ℝ) 1) :
    tsupport (fun x ↦ g x*conj (h x))⊆Set.Ioo (0:ℝ) 1 :=
  tsupport_mul_subset_left.trans hg

lemma diagonal_integral (g : ℝ → ℂ) :
    (∫ x : ℝ, g x*conj (g x))=((∫ x : ℝ, ‖g x‖^2 : ℝ) : ℂ) := by
  simp_rw [Complex.mul_conj,Complex.normSq_eq_norm_sq]
  exact integral_ofReal

/-- Fixed-data mean square sampling, including the equal-curvature case.
Separated blocks may be handled by the zero-product alternative. -/
theorem mode_energy {P : Type uP} [Fintype P] (g : P → ℝ → ℂ) (c : P → ℂ)
    (lam b d : P → ℝ) (hgc : ∀ i, HasCompactSupport (g i))
    (hgs : ∀ i, ContDiff ℝ ∞ (g i)) (hgi : ∀ i, tsupport (g i)⊆Set.Ioo (0:ℝ) 1)
    (hgb : ∀ i x, ‖g i x‖≤1)
    (hfreq : ∀ i j, i≠j → (lam i≠lam j ∨ ∀ l : ℤ, (l : ℝ)≠b i-b j) ∨
      ∀ x, g i x*conj (g j x)=0) :
    Tendsto (fun N : ℕ ↦ (∑ k : Fin N, ‖modeSum g c lam b d N k‖^2)/(N : ℝ))
      atTop (𝓝 (∑ i, ‖c i‖^2*(∫ x : ℝ, ‖g i x‖^2))) := by
  classical
  let V (i j : P) (N : ℕ) : ℂ := (c i*conj (c j))*realPhase (2*Real.pi*N*(d i-d j))*
    finiteAverage (fun x ↦ g i x*conj (g j x)) N (lam i-lam j) (b i-b j)
  have hV (i j : P) : Tendsto (V i j) atTop
      (𝓝 (if i=j then ((‖c i‖^2*(∫ x : ℝ, ‖g i x‖^2) : ℝ) : ℂ) else 0)) := by
    by_cases hij : i=j
    · subst j
      simp only [V,sub_self,mul_zero,realPhase_zero,mul_one]
      have h := (finiteAverage_diagonal (amplitude_pair_compact (hgc i))
        (amplitude_pair_smooth (hgs i) (hgs i)) (amplitude_pair_support (hgi i))).const_mul (c i*conj (c i))
      rw [diagonal_integral] at h
      simpa only [Complex.mul_conj,Complex.normSq_eq_norm_sq,
        Complex.ofReal_mul,ite_true] using h
    · rw [ite_eq_right hij]
      rw [tendsto_iff_norm_sub_tendsto_zero]
      simp only [sub_zero]
      have ht : Tendsto (fun N : ℕ ↦ ‖finiteAverage (fun x ↦ g i x*conj (g j x)) N
          (lam i-lam j) (b i-b j)‖) atTop (𝓝 0) := by
        rcases hfreq i j hij with hf | hz
        · apply finiteAverage_zero (amplitude_pair_compact (hgc i))
            (amplitude_pair_smooth (hgs i) (hgs j)) (amplitude_pair_support (hgi i))
            (by norm_num : (0:ℝ)≤1) ?_ (hf.imp (sub_ne_zero.mpr) id)
          intro x
          rw [norm_mul,norm_conj]
          exact (mul_le_of_le_one_left (norm_nonneg _) (hgb i x)).trans (hgb j x)
        · simp only [finiteAverage,hz,zero_mul,Finset.sum_const_zero,mul_zero,norm_zero]
          exact tendsto_const_nhds
      have he (N : ℕ) : ‖V i j N‖=‖c i*conj (c j)‖*
          ‖finiteAverage (fun x ↦ g i x*conj (g j x)) N (lam i-lam j) (b i-b j)‖ := by
        simp only [V,norm_mul,norm_realPhase,mul_one]
      simp_rw [he]
      simpa only [mul_zero] using ht.const_mul ‖c i*conj (c j)‖
  have ht := tendsto_finsetSum Finset.univ (fun i _ ↦
    tendsto_finsetSum Finset.univ (fun j _ ↦ hV i j))
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true] at ht
  have ht' := continuous_re.tendsto _ |>.comp ht
  simp only [Complex.re_sum,Complex.ofReal_re] at ht'
  apply ht'.congr'
  filter_upwards [] with N
  have he := norm_sq_modeSum g c lam b d N
  dsimp [V] at *
  rw [← he]
  simp only [Complex.ofReal_re]

end
end AsymptoticallyMinimalLittlewood.Sampling

namespace AsymptoticallyMinimalLittlewood.Sampling
noncomputable section
open scoped BigOperators Topology ContDiff ComplexConjugate
open MeasureTheory Filter Complex QuadraticTail

lemma norm_sum_sparse {P : Type uP} (s : Finset P) (f : P → ℂ) {K : ℝ}
    (hK : 0≤K) (hb : ∀ i∈s, ‖f i‖≤K)
    (hs : ∀ i∈s, ∀ j∈s, f i≠0 → f j≠0 → i=j) : ‖∑ i∈s, f i‖≤K := by
  classical
  by_cases h : ∃ i∈s, f i≠0
  · obtain ⟨i,hi,hfi⟩ := h
    rw [Finset.sum_eq_single i]
    · exact hb i hi
    · intro j hj hji
      by_contra hjf
      exact hji (hs j hj i hi hjf hfi)
    · exact fun hn ↦ (hn hi).elim
  · have hz : ∀ i∈s, f i=0 := by simpa using h
    simpa only [Finset.sum_eq_zero hz,norm_zero] using hK

lemma phase_modulate (lam b t x : ℝ) :
    phase lam (-b) x*realPhase (2*Real.pi*t*x)=phase lam (-(b+t)) x := by
  simp only [phase,realPhase,← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma mode_modulate {P : Type uP} [Fintype P] (g : P → ℝ → ℂ) (c : P → ℂ)
    (lam b d : P → ℝ) (N : ℕ) (t : ℝ) :
    ∑ k : Fin N, modeSum g c lam b d N k*realPhase (2*Real.pi*t*k)=
    ∑ i, (c i*realPhase (2*Real.pi*N*d i))*
      ∑ k : Fin N, g i ((k : ℝ)/N)*phase (lam i/N) (-(b i+t)) k := by
  simp only [modeSum,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  calc
    _ = (c i*realPhase (2*Real.pi*N*d i))*(g i ((k : ℝ)/N)*
      (phase (lam i/N) (-b i) k*realPhase (2*Real.pi*t*k))) := by ring
    _ = _ := by rw [phase_modulate]

/-- The fixed-data uniform circle estimate; the sparse-stationary hypothesis
will be discharged by the signed interval packing. -/
theorem mode_maximum {P : Type uP} [Fintype P] (g : P → ℝ → ℂ) (c : P → ℂ)
    (lam b d : P → ℝ) (hgc : ∀ i, HasCompactSupport (g i))
    (hgs : ∀ i, ContDiff ℝ ∞ (g i)) (hgi : ∀ i, tsupport (g i)⊆Set.Ioo (0:ℝ) 1)
    (hgb : ∀ i x, ‖g i x‖≤1) (hlam : ∀ i, lam i≠0)
    {K : ℝ} (hK : 0≤K) (hc : ∀ i, ‖c i‖/Real.sqrt |lam i|≤K)
    (hsparse : ∀ t : ℝ, ∀ i j : P, ∀ l m : ℤ,
      g i (((l : ℝ)-(b i+t))/lam i)≠0 → g j (((m : ℝ)-(b j+t))/lam j)≠0 →
      i=j ∧ l=m) :
    ∃ C : ℝ, 0≤C ∧ ∀ N : ℕ, 1≤N → ∀ t∈Set.Icc (0:ℝ) 1,
      ‖(1/(Real.sqrt N : ℂ))*∑ k : Fin N,
        modeSum g c lam b d N k*realPhase (2*Real.pi*t*k)‖≤K+C/N := by
  classical
  have hh (i : P) := uniform_poisson_chirp (hgc i) (hgs i)
    (A := 1) (B := |b i|+1) (by norm_num) (by positivity)
    (fun x hx ↦ by have := hgi i hx; constructor <;> linarith [this.1,this.2]) (hlam i)
  choose J C hC hest using hh
  let D := ∑ i, ‖c i‖*C i
  have hD : 0≤D := Finset.sum_nonneg (fun i _ ↦ mul_nonneg (norm_nonneg _) (hC i))
  refine ⟨D,hD,?_⟩
  intro N hN t ht
  have hNr : (1:ℝ)≤N := by exact_mod_cast hN
  have hN0 : 0<N := by omega
  have hb (i : P) : |b i+t|≤|b i|+1 :=
    (abs_add_le _ _).trans (add_le_add_right (show |t|≤1 by rw [abs_of_nonneg ht.1]; exact ht.2) _)
  let W (i : P) (l : ℤ) := (c i*realPhase (2*Real.pi*N*d i))*stationaryWave (g i) N (lam i) (b i+t) l
  let S : Finset (P × ℤ) := Finset.univ.sigma J |>.map
    ⟨fun p ↦ (p.1,p.2),by intro x y h; exact Sigma.ext (congrArg Prod.fst h) (heq_of_eq (congrArg Prod.snd h))⟩
  have hlead : ‖∑ i, ∑ l∈J i, W i l‖≤K := by
    have he : (∑ i, ∑ l∈J i, W i l)=∑ p∈S, W p.1 p.2 := by
      simp only [S,Finset.sum_map,Finset.sum_sigma]
      rfl
    rw [he]
    apply norm_sum_sparse S (fun p ↦ W p.1 p.2) hK
    · intro p _
      simp only [W,norm_mul,norm_realPhase,mul_one,stationaryWave_norm]
      calc
        _ ≤ ‖c p.1‖*(1/Real.sqrt |lam p.1|) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (hgb _ _) (Real.sqrt_nonneg _)) (norm_nonneg _)
        _ ≤ K := by simpa only [mul_one_div] using hc p.1
    · intro p _ q _ hp hq
      have hgp : g p.1 (((p.2 : ℝ)-(b p.1+t))/lam p.1)≠0 := by
        intro hz; apply hp; simp [W,stationaryWave,hz]
      have hgq : g q.1 (((q.2 : ℝ)-(b q.1+t))/lam q.1)≠0 := by
        intro hz; apply hq; simp [W,stationaryWave,hz]
      exact Prod.ext (hsparse t _ _ _ _ hgp hgq).1 (hsparse t _ _ _ _ hgp hgq).2
  let A (i : P) := (1/(Real.sqrt N : ℂ))*∑ k : Fin N,
    g i ((k : ℝ)/N)*phase (lam i/N) (-(b i+t)) k
  have hA (i : P) : ‖A i-∑ l∈J i, stationaryWave (g i) N (lam i) (b i+t) l‖≤C i/N := by
    have h := (hest i (N : ℝ) (b i+t) hNr (hb i)).2
    rw [tsum_eq_sum_fin _ (fun k hk ↦ by rw [sampled_support_zero (hgi i) hN0 hk,zero_mul])] at h
    simpa only [Int.cast_natCast] using h
  have herr : ‖(∑ i, (c i*realPhase (2*Real.pi*N*d i))*A i)-
      ∑ i, ∑ l∈J i, W i l‖≤D/N := by
    simp only [W,← Finset.mul_sum,← Finset.sum_sub_distrib,← mul_sub]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ i, ‖c i‖*(C i/N) := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [norm_mul,norm_realPhase,mul_one] using
          mul_le_mul_of_nonneg_left (hA i) (norm_nonneg (c i))
      _ = D/N := by simp only [D,Finset.sum_div,mul_div_assoc]
  have he : (1/(Real.sqrt N : ℂ))*∑ k : Fin N,
      modeSum g c lam b d N k*realPhase (2*Real.pi*t*k)=
      ∑ i, (c i*realPhase (2*Real.pi*N*d i))*A i := by
    rw [mode_modulate,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [A]
    ring
  rw [he]
  exact (norm_le_norm_sub_add _ _).trans ((add_le_add herr hlead).trans_eq (add_comm _ _))

end
end AsymptoticallyMinimalLittlewood.Sampling

end OAI
