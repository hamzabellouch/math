import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.CubePolynomials01
import OAI.Combinatorics.SumProduct.Alignment.RationalLattice01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
open scoped commutatorElement
end
 

 
section
open scoped commutatorElement
noncomputable section
namespace CubeFaces
variable {G A : Type*} [Group G] [Group A]

def Filtration.pullback (H : Filtration G) (φ : A →* G) : Filtration A where
  level i := (H.level i).comap φ
  antitone i j hij := Subgroup.comap_mono (H.antitone hij)
  commutator_le i j := by
    apply Subgroup.commutator_le.mpr
    intro a ha b hb
    change φ ⁅a,b⁆ ∈ H.level (i+j)
    rw [map_commutatorElement]
    exact H.commutator_le i j (Subgroup.commutator_mem_commutator ha hb)

 

def Filtration.refine (H : Filtration G) (K : Subgroup G)
    (hcomm : ∀ a b : G, ⁅a,b⁆ ∈ K) : Filtration G where
  level i := if i < 2 then H.level i else H.level i ⊓ K
  antitone := by
    intro i j hij
    by_cases hi : i < 2
    · simp only [hi,ite_true]
      split_ifs
      · exact H.antitone hij
      · exact inf_le_left.trans (H.antitone hij)
    · have hj : ¬ j < 2 := by omega
      simp only [hi,hj,ite_false]
      exact inf_le_inf (H.antitone hij) le_rfl
  commutator_le := by
    intro i j
    apply Subgroup.commutator_le.mpr
    intro a ha b hb
    have hia : a ∈ H.level i := by split_ifs at ha <;> aesop
    have hjb : b ∈ H.level j := by split_ifs at hb <;> aesop
    have hc := H.commutator_le i j (Subgroup.commutator_mem_commutator hia hjb)
    split_ifs
    · exact hc
    · exact ⟨hc,hcomm a b⟩
end CubeFaces

namespace CubePolynomials
open CubeFaces
variable {G A : Type*} [Group G] [Group A]

 

theorem pullback_mem (H : Filtration G) (φ : A →* G) (hφ : Function.Injective φ)
    (q k : ℕ) (hbot : H.level (k+q) = ⊥) (f : ℤ → A)
    (hf : (fun n => φ (f n)) ∈ polynomials H k) :
    f ∈ polynomials (H.pullback φ) k := by
  induction q generalizing k f with
  | zero =>
    have he : f = 1 := by
      funext n
      apply hφ
      have hv := eval_mem hf n
      have hb : H.level k = ⊥ := by simpa using hbot
      simpa [hb] using hv
    rw [he]
    exact (polynomials _ _).one_mem
  | succ q ih =>
    apply mem_of_derivatives
    · intro n
      exact eval_mem hf n
    · intro t
      apply ih (k+1) (by convert hbot using 1; congr 1; omega)
      convert derivative_mem hf t using 1
      ext n
      simp [shift,map_mul,map_inv]

 

theorem refine_mem (H : Filtration G) (K : Subgroup G)
    (hcomm : ∀ a b : G, ⁅a,b⁆ ∈ K) (q k : ℕ) (hbot : H.level (k+q) = ⊥)
    (f : ℤ → G) (hf : f ∈ polynomials H k) (hK : ∀ n, f n ∈ K) :
    f ∈ polynomials (H.refine K hcomm) k := by
  induction q generalizing k f with
  | zero =>
    have he : f = 1 := by
      funext n
      have hv := eval_mem hf n
      have hb : H.level k = ⊥ := by simpa using hbot
      simpa [hb] using hv
    rw [he]
    exact (polynomials _ _).one_mem
  | succ q ih =>
    apply mem_of_derivatives
    · intro n
      change f n ∈ (if k < 2 then H.level k else H.level k ⊓ K)
      split_ifs
      · exact eval_mem hf n
      · exact ⟨eval_mem hf n,hK n⟩
    · intro t
      apply ih (k+1) (by convert hbot using 1; congr 1; omega)
        _ (derivative_mem hf t)
      intro n
      exact K.mul_mem (K.inv_mem (hK n)) (hK (n+t))

 

theorem refine_of_linear_coset (H : Filtration G) (K : Subgroup G)
    (hcomm : ∀ a b : G, ⁅a,b⁆ ∈ K) (s : ℕ) (hbot : H.level s = ⊥)
    (f : ℤ → G) (hf : f ∈ polynomials H 0) (a : G) (ha : a ∈ H.level 1)
    (hK : ∀ n, f n * (a^n)⁻¹ ∈ K) : f ∈ polynomials (H.refine K hcomm) 0 := by
  have hl : (fun n : ℤ => a^n) ∈ polynomials H 0 := by
    simpa using NilpotentTaylor.binomial_mem (H:=H) 1 0 a ha
  have hl' : (fun n : ℤ => a^n) ∈ polynomials (H.refine K hcomm) 0 := by
    apply (by simpa using NilpotentTaylor.binomial_mem (H:=H.refine K hcomm) 1 0 a ha)
  have hr := refine_mem H K hcomm s 0 (by simpa using hbot)
    (f*(fun n : ℤ => a^n)⁻¹) ((polynomials H 0).mul_mem hf ((polynomials H 0).inv_mem hl)) hK
  have he : (f*(fun n : ℤ => a^n)⁻¹) * (fun n : ℤ => a^n) = f := by group
  rw [← he]
  exact (polynomials _ _).mul_mem hr hl'

end CubePolynomials
end
end
 

 
section
namespace RationalFactorPeriods
noncomputable section
lemma eval_desc (n : ℤ) (j : ℕ) :
    (descPochhammer ℤ j).eval n = (j.factorial : ℤ) * Ring.choose n j := by
  have h := Ring.descPochhammer_eq_factorial_smul_choose n j
  rw [← Polynomial.aeval_eq_smeval] at h
  simpa using h

 

lemma choose_period_dvd (m : ℕ) {j d : ℕ} (hj : j ≤ d) (n : ℤ) :
    (m : ℤ) ∣ Ring.choose (n + (m * d.factorial : ℕ)) j - Ring.choose n j := by
  have h := Polynomial.sub_dvd_eval_sub (n + (m*d.factorial : ℕ)) n
    (descPochhammer ℤ j)
  rw [add_sub_cancel_left,eval_desc,eval_desc,← mul_sub] at h
  have hfac : (j.factorial : ℤ) ∣ (d.factorial : ℤ) :=
    Int.natCast_dvd_natCast.mpr (Nat.factorial_dvd_factorial hj)
  have hdiv : (j.factorial : ℤ) * m ∣ (m*d.factorial : ℕ) := by
    rw [Nat.cast_mul,mul_comm (j.factorial : ℤ)]
    exact mul_dvd_mul_left (m : ℤ) hfac
  exact (Int.mul_dvd_mul_iff_left (by exact_mod_cast j.factorial_ne_zero)).mp (hdiv.trans h)

variable {G : Type*} [Group G]
lemma zpow_eq_of_sub_dvd {a : G} {m : ℕ} (ha : a^m = 1) {u v : ℤ}
    (h : (m : ℤ) ∣ u-v) : a^u = a^v := by
  obtain ⟨z,hz⟩ := h
  have he : u = (m : ℤ)*z+v := by omega
  rw [he,zpow_add,zpow_mul,zpow_natCast,ha,one_zpow,one_mul]

 

def orderedWord {k : ℕ} (a : Fin k → G) (j : Fin k → ℕ) (b : ℤ) : G :=
  ((List.finRange k).map (fun i => a i ^ Ring.choose b (j i))).prod

lemma orderedWord_map {K : Type*} [Group K] (φ : G →* K) {k : ℕ}
    (a : Fin k → G) (j : Fin k → ℕ) (b : ℤ) :
    φ (orderedWord a j b) = orderedWord (fun i => φ (a i)) j b := by
  simp [orderedWord,map_list_prod,List.map_map,Function.comp_def]

lemma orderedWord_congr {k : ℕ} {a a' : Fin k → G}
    (ha : ∀ i, a i = a' i) (j : Fin k → ℕ) (b : ℤ) :
    orderedWord a j b = orderedWord a' j b := by
  have h : a = a' := funext ha
  rw [h]

lemma orderedWord_periodic {k : ℕ} (a : Fin k → G) (j : Fin k → ℕ)
    (m s : ℕ) (ha : ∀ i, a i ^ m = 1) (hj : ∀ i, j i ≤ s) :
    Function.Periodic (orderedWord a j) (m * s.factorial : ℕ) := by
  intro b
  unfold orderedWord
  congr 1
  apply List.map_congr_left
  intro i _
  exact zpow_eq_of_sub_dvd (ha i) (choose_period_dvd m (hj i) b)

lemma finite_image_periodic {K : Type*} [Group K] [Fintype K]
    (φ : G →* K) {k : ℕ} (a : Fin k → G) (j : Fin k → ℕ)
    (s : ℕ) (hj : ∀ i, j i ≤ s) :
    Function.Periodic (fun b => φ (orderedWord a j b))
      (Fintype.card K * s.factorial : ℕ) := by
  intro b
  simp only [orderedWord_map]
  exact orderedWord_periodic (fun i => φ (a i)) j (Fintype.card K) s
    (fun _ => pow_card_eq_one) hj b

lemma finite_image_stabilizes {K : Type*} [Group K] [Finite K]
    (φ : G →* K) {k : ℕ} (a : ℕ → Fin k → G) (j : Fin k → ℕ) :
    ∃ u : ℕ → ℕ, StrictMono u ∧ ∀ l b,
      φ (orderedWord (a (u l)) j b) = φ (orderedWord (a (u 0)) j b) := by
  classical
  let F : ℕ → (Fin k → K) := fun l i => φ (a l i)
  obtain ⟨v,hv⟩ := Finite.exists_infinite_fiber F
  have hi : (Set.ofPred (fun l => F l = v)).Infinite := Set.infinite_coe_iff.mp hv
  refine ⟨Nat.nth (fun l => F l = v),Nat.nth_strictMono hi,?_⟩
  intro l b
  simp only [orderedWord_map]
  apply orderedWord_congr
  intro i
  have hl := congrFun (Nat.nth_mem_of_infinite hi l) i
  have hz := congrFun (Nat.nth_mem_of_infinite hi 0) i
  exact hl.trans hz.symm

lemma coset_pattern_stabilizes (Γ : Subgroup G) [Γ.FiniteIndex]
    {k : ℕ} (a : ℕ → Fin k → G) (j : Fin k → ℕ)
    (s : ℕ) (hj : ∀ i, j i ≤ s) :
    ∃ (u : ℕ → ℕ) (T : ℕ), StrictMono u ∧ 0 < T ∧
      (∀ l b, (QuotientGroup.mk (orderedWord (a (u l)) j b) : G ⧸ Γ) =
        QuotientGroup.mk (orderedWord (a (u 0)) j b)) ∧
      Function.Periodic
        (fun b => (QuotientGroup.mk (orderedWord (a (u 0)) j b) : G ⧸ Γ)) (T : ℤ) := by
  classical
  let : Fintype (G ⧸ Γ) := Fintype.ofFinite _
  let K := Equiv.Perm (G ⧸ Γ)
  let φ : G →* K := MulAction.toPermHom G (G ⧸ Γ)
  obtain ⟨u,hu,he⟩ := finite_image_stabilizes φ a j
  refine ⟨u,Fintype.card K * s.factorial,hu,
    Nat.mul_pos Fintype.card_pos s.factorial_pos,?_,?_⟩
  · intro l b
    have h := congrArg (fun e : K => e (QuotientGroup.mk (1:G))) (he l b)
    simpa [φ,K,MulAction.toPermHom] using h
  · intro b
    have h := congrArg (fun e : K => e (QuotientGroup.mk (1:G)))
      (finite_image_periodic φ (a (u 0)) j s hj b)
    simpa [φ,K,MulAction.toPermHom] using h

lemma periodic_mod {α : Type*} {f : ℤ → α} {T : ℤ}
    (hf : Function.Periodic f T) (b : ℤ) : f (b % T) = f b := by
  have h := hf.sub_int_mul_eq (x := b) (b / T)
  simpa [Int.emod_def,mul_comm] using h

 

theorem rational_right_factors [TopologicalSpace G] [IsTopologicalGroup G]
    [PreconnectedSpace G] [LocallyCompactSpace G] [T2Space G] {n k : ℕ}
    (c : RationalLattice.RealCoordinates G n) (Γ : Subgroup G) [DiscreteTopology Γ]
    (hΓrat : Γ ≤ RationalLattice.rationalSubgroup c)
    (C : Set G) (hC : IsCompact C) (hreps : ∀ g : G, ∃ x ∈ C, x⁻¹*g ∈ Γ)
    (v : Fin k → G) (hv : ∀ i, RationalLattice.IsRational c (v i))
    (m : ℕ → Fin k → ℤ) (j : Fin k → ℕ) (s : ℕ) (hj : ∀ i, j i ≤ s) :
    ∃ (u : ℕ → ℕ) (T : ℕ) (σ : Fin T → G), StrictMono u ∧ 0 < T ∧
      (∀ r, RationalLattice.IsRational c (σ r)) ∧
      ∀ l b, ∃ r : Fin T, (r.val : ℤ) = b % (T : ℤ) ∧
        (QuotientGroup.mk (orderedWord (fun i => v i ^ m (u l) i) j b) : G ⧸ Γ) =
          QuotientGroup.mk (σ r) := by
  classical
  let S := Finset.univ.image v
  have hSrat : ∀ g ∈ S, RationalLattice.IsRational c g := by
    intro g hg
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hg
    exact hv i
  obtain ⟨H,hΓH,hSH,hHrat,hHd,hHi⟩ :=
    RationalLattice.finite_rational_extension c Γ hΓrat C hC hreps S hSrat
  let : (Γ.subgroupOf H).FiniteIndex := hHi
  have hvH (i : Fin k) : v i ∈ H := hSH (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
  let a : ℕ → Fin k → H := fun l i => ⟨v i ^ m l i,H.zpow_mem (hvH i) _⟩
  obtain ⟨u,T,hu,hT,hfix,hper⟩ := coset_pattern_stabilizes (Γ.subgroupOf H) a j s hj
  let σ : Fin T → G := fun r => (orderedWord (a (u 0)) j (r.val : ℤ) : H)
  refine ⟨u,T,σ,hu,hT,?_,?_⟩
  · intro r
    exact hHrat (orderedWord (a (u 0)) j (r.val : ℤ)).property
  · intro l b
    have hnonneg : 0 ≤ b % (T : ℤ) := Int.emod_nonneg _ (by omega)
    have hlt : b % (T : ℤ) < T := Int.emod_lt_of_pos _ (by omega)
    let r : Fin T := ⟨(b % (T : ℤ)).toNat,by omega⟩
    have hr : (r.val : ℤ) = b % (T : ℤ) := Int.toNat_of_nonneg hnonneg
    refine ⟨r,hr,?_⟩
    have he : (QuotientGroup.mk (orderedWord (a (u l)) j b) : H ⧸ Γ.subgroupOf H) =
        QuotientGroup.mk (orderedWord (a (u 0)) j (r.val : ℤ)) := by
      rw [hr]
      exact (hfix l b).trans (periodic_mod hper b).symm
    have hmem := QuotientGroup.eq.mp he
    have hquot : (QuotientGroup.mk ((orderedWord (a (u l)) j b : H) : G) : G ⧸ Γ) =
        QuotientGroup.mk (σ r) := QuotientGroup.eq.mpr hmem
    have hmap : ((orderedWord (a (u l)) j b : H) : G) =
        orderedWord (fun i => v i ^ m (u l) i) j b :=
      orderedWord_map H.subtype (a (u l)) j b
    rw [hmap] at hquot
    exact hquot

end
end RationalFactorPeriods

end
end
end
end

end OAI
