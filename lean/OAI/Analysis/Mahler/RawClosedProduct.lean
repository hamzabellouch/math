import OAI.Analysis.Mahler.RawAlternatingCalculus

namespace OAI

namespace Mahler
noncomputable section
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

@[simp] lemma raw_wedge_zero_left (b : E [⋀^κ]→ₗ[ℝ] ℂ) :
    wedge (0 : E [⋀^ι]→ₗ[ℝ] ℂ) b = 0 := by
  simpa only [zero_smul] using wedge_smul_left (0 : ℂ) (0 : E [⋀^ι]→ₗ[ℝ] ℂ) b

@[simp] lemma raw_wedge_zero_right (a : E [⋀^ι]→ₗ[ℝ] ℂ) :
    wedge a (0 : E [⋀^κ]→ₗ[ℝ] ℂ) = 0 := by
  simpa only [zero_smul] using wedge_smul_right (0 : ℂ) a (0 : E [⋀^κ]→ₗ[ℝ] ℂ)

/-- Adjoin the actual directional derivative as the first raw slot. -/
def rawPrefix (D : E →ₗ[ℝ] MultilinearMap ℝ (fun _ : ι => E) ℂ) :
    MultilinearMap ℝ (fun _ : Fin 1 ⊕ ι => E) ℂ :=
  (MultilinearMap.ofSubsingleton ℝ E _ (0 : Fin 1) D).uncurrySum

omit [Fintype ι] [DecidableEq ι] in
@[simp] lemma rawPrefix_apply [Fintype ι] [DecidableEq ι] (D : E →ₗ[ℝ] MultilinearMap ℝ (fun _ : ι => E) ℂ)
    (v : Fin 1 ⊕ ι → E) :
    rawPrefix D v = D (v (Sum.inl 0)) (fun i => v (Sum.inr i)) := rfl

def rawProductVariation (a : MultilinearMap ℝ (fun _ : ι => E) ℂ)
    (Da : E →ₗ[ℝ] MultilinearMap ℝ (fun _ : ι => E) ℂ)
    (b : MultilinearMap ℝ (fun _ : κ => E) ℂ)
    (Db : E →ₗ[ℝ] MultilinearMap ℝ (fun _ : κ => E) ℂ) :
    E →ₗ[ℝ] MultilinearMap ℝ (fun _ : ι ⊕ κ => E) ℂ where
  toFun v := rawProduct (Da v) b + rawProduct a (Db v)
  map_add' v w := by ext z; simp [rawProduct_apply]; ring
  map_smul' r v := by ext z; simp [rawProduct_apply]; ring

/-- Move a distinguished derivative slot past the left factor without
changing the order within either factor. -/
def rawMoveDerivative (ι κ : Type*) : ι ⊕ (Fin 1 ⊕ κ) ≃ Fin 1 ⊕ (ι ⊕ κ) :=
  (Equiv.sumAssoc ι (Fin 1) κ).symm |>.trans
    ((Equiv.sumCongr (Equiv.sumComm ι (Fin 1)) (Equiv.refl κ)).trans
      (Equiv.sumAssoc (Fin 1) ι κ))

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
/-- Every product-rule term, with its explicit slot placement. -/
theorem rawPrefix_productVariation [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] (a : MultilinearMap ℝ (fun _ : ι => E) ℂ)
    (Da : E →ₗ[ℝ] MultilinearMap ℝ (fun _ : ι => E) ℂ)
    (b : MultilinearMap ℝ (fun _ : κ => E) ℂ)
    (Db : E →ₗ[ℝ] MultilinearMap ℝ (fun _ : κ => E) ℂ) :
    rawPrefix (rawProductVariation a Da b Db) =
      (rawProduct (rawPrefix Da) b).domDomCongr (Equiv.sumAssoc (Fin 1) ι κ) +
      (rawProduct a (rawPrefix Db)).domDomCongr (rawMoveDerivative ι κ) := by
  ext v
  rfl

/-- If both factors are closed after alternation, their full product-rule
variation is closed. This retains both placement terms before cancelling. -/
theorem rawPrefix_productVariation_closed
    (a : MultilinearMap ℝ (fun _ : ι => E) ℂ)
    (Da : E →ₗ[ℝ] MultilinearMap ℝ (fun _ : ι => E) ℂ)
    (b : MultilinearMap ℝ (fun _ : κ => E) ℂ)
    (Db : E →ₗ[ℝ] MultilinearMap ℝ (fun _ : κ => E) ℂ)
    (ha : (rawPrefix Da).alternatization = 0)
    (hb : (rawPrefix Db).alternatization = 0) :
    (rawPrefix (rawProductVariation a Da b Db)).alternatization = 0 := by
  rw [rawPrefix_productVariation, map_add, raw_alternatization_reindex,
    raw_alternatization_reindex, rawProduct_alternatization, rawProduct_alternatization,
    ha, hb]
  simp

/-- If only the right factor is closed, the entire derivative is exactly
the left-factor term, with its reassociation shown. -/
theorem rawPrefix_productVariation_right_closed
    (a : MultilinearMap ℝ (fun _ : ι => E) ℂ)
    (Da : E →ₗ[ℝ] MultilinearMap ℝ (fun _ : ι => E) ℂ)
    (b : MultilinearMap ℝ (fun _ : κ => E) ℂ)
    (Db : E →ₗ[ℝ] MultilinearMap ℝ (fun _ : κ => E) ℂ)
    (hb : (rawPrefix Db).alternatization = 0) :
    (rawPrefix (rawProductVariation a Da b Db)).alternatization =
      (wedge (rawPrefix Da).alternatization b.alternatization).domDomCongr
        (Equiv.sumAssoc (Fin 1) ι κ) := by
  rw [rawPrefix_productVariation, map_add, raw_alternatization_reindex,
    raw_alternatization_reindex, rawProduct_alternatization, rawProduct_alternatization, hb]
  simp

end
end Mahler

end OAI
