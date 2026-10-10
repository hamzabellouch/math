import OAI.Combinatorics.HadwigerCounterexample.ConditionalCellEntropy

namespace OAI

/-! # Image Character Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Finset
open scoped BigOperators
variable {p : Shape} {n N : ℕ}
abbrev DTuple {p : Shape} (r : Place p → ℕ) (N : ℕ) :=
  ∀ z, Mat (Fin N) (Fin (r z))
abbrev WTuple {p : Shape} (r : Place p → ℕ) (n : ℕ) :=
  ∀ z, Mat (JointIdx p n) (Fin (r z))

def flipEquiv (p : Shape) : Place p ≃ Place p :=
  ⟨flipZ p,flipZ p,fun i => flipZ_flip i,fun i => flipZ_flip i⟩

variable {r : Place p→ℕ}

theorem tuple_dim :
    dim (DTuple (p:=p) r N)=N*∑ z : Place p,r z := by
  unfold DTuple dim
  rw [finrank_pi_fintype,Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact (dim_mat _ _).trans (by simp)

def projTuple (p : Shape) {n N} (r : Place p→ℕ) (A : WTuple (p:=p) r n)
    (x : Place p ≃ Place p) (w : UnitType p n N) : DTuple (p:=p) r N :=
  fun z => images w (x z) * A z

theorem cap_tuple (p : Shape) {n N} (r : Place p → ℕ) (A : WTuple (p:=p) r n)
    (x : Place p ≃ Place p) {w : Wgt (UnitType p n N)} {f : Pin p n N} {ζ : ℝ}
    (h : ∀ z, Function.Injective (A z).mulVec)
    (hf : ∀ z, Disjoint (colSp (A z)) (f.sp (x z)))
    (hw : SubLaw w) (hc : f.clear ζ w) :
    ∀ y, mapW w (projTuple p r A x) y ≤ fee N ζ (∑ z,r z) := by
  classical
  intro y
  let P := fun z : UnitType p n N => projTuple p r A x z=y
  change pr w P ≤ _
  by_cases hP : 0 < pr w P
  · obtain ⟨a,ha,hA⟩ := exists_of_pr_pos hw.nz hP
    let D : Plan p n := fun z => colSp (A (x.symm z))
    let c := Pin.make D a
    have h1 : pr w P ≤ pr w c.agree := by
      refine pr_mono hw.nz fun w hw z t ht => ?_
      change t∈colSp (A (x.symm z)) at ht
      obtain ⟨u,rfl⟩ := ht
      change _ *ᵥ _ = images a z *ᵥ _
      have hh := congr_fun (hw.trans ha.symm) (x.symm z)
      unfold projTuple at hh; rw [x.apply_symm_apply] at hh
      rw [mulVecLin_apply,mulVec_mulVec,mulVec_mulVec,hh]
    have h2 : planNew f.sp D=∑ z,r z := by
      rw [plan_new_disjoint f.sp D]
      · have hh (z) : dim (D z)=r (x.symm z) := (mrk_inj.mp (h (x.symm z))).trans
          (Fintype.card_fin _)
        unfold planRank
        simp_rw [hh]
        exact Equiv.sum_comp _ _
      · intro z
        have hh := hf (x.symm z)
        rw [x.apply_symm_apply] at hh; exact hh.symm
    rw [← h2]
    exact h1.trans (hc c)
  exact (not_lt.mp hP).trans (bp_pos _).le

variable {I J : Type} [Fintype I] [Fintype J]
theorem mpair_nondeg (M : Mat I J) (h : mpair M=0) : M=0 := by
  classical
  apply evmat_ext; intro x y
  rw [←mpair_outer,h]; simp [evmat]

def tupleB (p : Shape) (r : Place p → ℕ) (N : ℕ) :
    DTuple (p:=p) r N →ₗ[F] DTuple (p:=p) r N →ₗ[F] F where
  toFun x := ∑ z : Place p, mpair (x z) ∘ₗ LinearMap.proj z
  map_add' x y := LinearMap.ext fun v => by
    simp only [LinearMap.sum_apply,LinearMap.comp_apply,Pi.add_apply,LinearMap.add_apply,
      mpair_add,Finset.sum_add_distrib]
  map_smul' a x := LinearMap.ext fun v => by
    simp only [LinearMap.sum_apply,LinearMap.comp_apply,Pi.smul_apply,RingHom.id_apply,
      LinearMap.smul_apply,mpair_smul,Finset.mul_sum,smul_eq_mul]

theorem tupleB_val (x y : DTuple (p:=p) r N) :
    tupleB p r N x y=∑ z,mpair (x z) (y z) := by
  simp only [tupleB,LinearMap.sum_apply,LinearMap.coe_mk,AddHom.coe_mk]; rfl

theorem tupleB_inj (p : Shape) (r : Place p→ℕ) (N : ℕ) :
    Function.Injective (tupleB p r N) := by
  classical
  rw [← LinearMap.ker_eq_bot]
  refine le_bot_iff.mp (fun x hx => ?_)
  change tupleB p r N x = 0 at hx
  have hh (z : Place p) : mpair (x z)=0 := by
    refine LinearMap.ext (fun M => ?_)
    have he := LinearMap.congr_fun hx (Pi.single z M)
    rw [tupleB_val,Finset.sum_eq_single z] at he
    · rwa [Pi.single_eq_same] at he
    · intro i _ hi; simp [hi]
    simp
  have h' : x=0 := funext fun z => mpair_nondeg _ (hh z)
  rw [h']; exact Submodule.zero_mem _

theorem charImages (p : Shape) {n N} (r : Place p → ℕ) (A B : WTuple (p:=p) r n)
    {u w : Wgt (UnitType p n N)} (hu : IsLaw u) (hw : IsLaw w) {f b : Pin p n N}
    (hc : f.clear 0.05 u) (hd : b.clear 0.05 w)
    (hA : ∀ z,Function.Injective (A z).mulVec ∧ Disjoint (colSp (A z)) (f.sp z))
    (hB : ∀ z,Function.Injective (B z).mulVec ∧ Disjoint (colSp (B z)) (b.sp (flipZ p z)))
    (hr : 1 ≤ ∑ z,r z) :
    |avg (pairW u w) (fun x => wsign (tupleB p r N (projTuple p r A (Equiv.refl _) x.1)
      (projTuple p r B (flipEquiv p) x.2)))| ≤ bp (-0.45*N) := by
  classical
  let H := tupleB p r N
  let g := projTuple p r A (Equiv.refl _) (N:=N)
  let g' := projTuple p r B (flipEquiv p) (N:=N)
  let q := mapW u g
  let v := mapW w g'
  let t := ∑ i,r i
  have he :
      avg (pairW u w) (fun x => wsign (H (g x.1) (g' x.2))) =
        avg v (fun y => avg q (fun x => wsign (H x y))) := by
    rw [pairW_avg]
    unfold q v
    rw [mapW_avg]
    simp_rw [mapW_avg]
    exact avg_avg ..
  have hp (x) : q x ≤ fee N 0.05 t :=
    cap_tuple p r A (Equiv.refl _) (fun z => (hA z).1) (fun z => (hA z).2) hu.sub hc x
  have hq (x) : v x ≤ fee N 0.05 t :=
    cap_tuple p r B (flipEquiv p) (fun z => (hB z).1) (fun z => (hB z).2) hw.sub hd x
  have hh := walsh_mass H (tupleB_inj p r N) q v (fun _ => 1) (fun _ => 1)
    (fun _ => by norm_num) (fun _ => by norm_num) (mapW_law hu g).sub (mapW_law hw g').sub hp hq
  change |avg (pairW u w) _|≤_
  rw [he]
  let R := avg v (fun y => avg q (fun x => wsign (H x y)))
  have hi : R^2 ≤ (bp (-0.45*N))^2 := by
    simp only [one_mul] at hh
    apply le_trans hh
    rw [card_space,tuple_dim]
    unfold fee
    change bp (↑(N*t))* _ * _ ≤ _
    rw [←bp_add,←bp_add,pow_two,←bp_add]
    apply bp_le
    have h' : 1 ≤ (t:ℝ) := by exact_mod_cast hr
    push_cast
    have hx := mul_le_mul_of_nonneg_left h' (show 0≤(N:ℝ) from Nat.cast_nonneg _)
    linarith only [hx]
  exact le_of_pow_le_pow_left₀ (show (2:ℕ) ≠ 0 by decide) (bp_pos _).le
    (sq_abs R ▸ hi)

end HadwigerCounterexample

end

end OAI
